module

public import CFSG.Quasithin.H13.QRCPairedDihedral
public import CFSG.Quasithin.H13.QRCPairedHigh

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.ShultStronglyClosedTI
  CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open scoped MatrixGroups

variable {A : Type*} [Group A] [Finite A] {k : Type} [Field k] [CharP k 2] [Finite k] {n : ℕ}
  {K₁ K₂ : Subgroup A}

theorem exists_ne_zero_sq_ne_one {F : Type*} [Field F] [CharP F 2] [Finite F]
    (h : 2 < Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have h1 : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  obtain ⟨u, hu⟩ := @exists_ne Fˣ (Finite.one_lt_card_iff_nontrivial.1 h1) 1
  refine ⟨u, u.ne_zero, fun h2 => hu (Units.ext ?_)⟩
  apply frobenius_inj F 2
  simpa [frobenius_def] using h2

theorem paired_quotient (hk : Nat.card k = 2 ^ n) (hn : 2 ≤ n)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥) (hKn : (K₁ ⊔ K₂).Normal)
    (hCK : ∀ a : A, (∀ x ∈ K₁ ⊔ K₂, a * x = x * a) → a = 1) (S : Sylow 2 A)
    (hKS : K₁ ⊔ K₂ ⊔ (S : Subgroup A) = ⊤) (θ₁ : K₁ ≃* SL(2, k)) (θ₂ : K₂ ≃* SL(2, k))
    (hsw : ∃ a : A, K₁.map (MulAut.conj a).toMonoidHom = K₂) {B E : Subgroup A}
    (hSB : (S : Subgroup A) ≤ B) (hBtop : B < ⊤)
    (hBmax : ∀ Y : Subgroup A, (S : Subgroup A) ≤ Y → Y < ⊤ → Y ≤ B)
    [IsElementaryAbelian 2 E] (hEO : E ≤ inSubgroup (pCore 2) B)
    (hSE : (S : Subgroup A) ≤ normalizer (E : Set A)) (hE4 : 4 ≤ Nat.card E) :
    ∃ (θ₁' : K₁ ≃* SL(2, k)) (θ₂' : K₂ ≃* SL(2, k)) (R : Subgroup A),
      IsPGroup 2 R ∧ (K₁ ⊔ K₂) ⊓ R = ⊥ ∧ (K₁ ⊔ K₂) ⊔ R = ⊤ ∧
      (∀ r ∈ R, IsFieldPerm θ₁' θ₂' r) ∧ (∃ r ∈ R, K₁.map (MulAut.conj r).toMonoidHom = K₂) ∧
      (S : Subgroup A) = stdSub θ₁' (sl2UpperUnipotentSubgroup k) ⊔
        stdSub θ₂' (sl2UpperUnipotentSubgroup k) ⊔ R ∧
      B = stdSub θ₁' (sl2Borel k) ⊔ stdSub θ₂' (sl2Borel k) ⊔ R ∧
      E ≤ stdSub θ₁' (sl2UpperUnipotentSubgroup k) ⊔ stdSub θ₂' (sl2UpperUnipotentSubgroup k) ∧
      (S : Subgroup A) ⊓ K₁ = stdSub θ₁' (sl2UpperUnipotentSubgroup k) ∧
      B ⊓ K₁ = stdSub θ₁' (sl2Borel k) ∧
      (E ⊔ K₂) ⊓ K₁ ≤ stdSub θ₁' (sl2UpperUnipotentSubgroup k) ∧
      (E ⊔ K₁) ⊓ K₂ ≤ stdSub θ₂' (sl2UpperUnipotentSubgroup k) ∧
      ∃ r : ℕ, 1 ≤ r ∧ Nat.card ↥((E ⊔ K₂) ⊓ K₁) = 2 ^ r ∧
        Nat.card ↥((E ⊔ K₁) ⊓ K₂) = 2 ^ r ∧
      ∃ (x₁ : A) (L₁ : Subgroup A), x₁ ∈ K₁ ∧
        L₁ = (E ⊔ K₂) ⊓ K₁ ⊔ conjugate ((E ⊔ K₂) ⊓ K₁) x₁ ∧ x₁ ∈ L₁ ∧ L₁ ≤ K₁ ∧
        E ⊔ conjugate E x₁ = L₁ ⊔ (E ⊔ K₁) ⊓ K₂ ∧
        IsSylowOf 2 ((S : Subgroup A) ⊓ L₁) L₁ ∧ kerIn (B ⊓ L₁) L₁ = ⊥ ∧
        inSubgroup (pCore 2) L₁ = ⊥ ∧ inSubgroup (pCore 2) (B ⊓ L₁) = (S : Subgroup A) ⊓ L₁ ∧
        (2 ≤ r → ∃ f : ℕ, 2 ≤ f ∧ r ≤ f ∧ f ∣ n ∧
          ∃ e : L₁ ≃* PSL2MatrixGroup (GaloisField 2 f),
            ((B ⊓ L₁).subgroupOf L₁).map e.toMonoidHom = psl2Borel (GaloisField 2 f) ∧
            (((S : Subgroup A) ⊓ L₁).subgroupOf L₁).map e.toMonoidHom =
              psl2UpperUnipotentSubgroup (GaloisField 2 f)) ∧
        (r = 1 → Nat.card E = 4 ∧ E = (E ⊔ K₂) ⊓ K₁ ⊔ (E ⊔ K₁) ⊓ K₂ ∧
          Nonempty (L₁ ≃* DihedralGroup 3) ∧ B ⊓ L₁ = (E ⊔ K₂) ⊓ K₁ ∧
          (S : Subgroup A) ⊓ L₁ = (E ⊔ K₂) ⊓ K₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hKn
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  obtain ⟨θ₁, θ₂, R, hRS, hR2, hKR, hKRt, hRperm, hRsw, hS⟩ :=
    exists_fieldPerm_coords hk hn hc hd hKn S hKS θ₁ θ₂ hsw
  obtain ⟨hB, hBK, hSK, hO2B⟩ :=
    paired_borel hk hn hc hd hKn hCK S hKR hKRt hRperm hRsw hS hSB hBtop hBmax
  set Ū := sl2UpperUnipotentSubgroup k with hŪ
  set U₁ := stdSub θ₁ Ū with hU₁
  set U₂ := stdSub θ₂ Ū with hU₂
  set E₁ := (E ⊔ K₂) ⊓ K₁ with hE₁
  set E₂ := (E ⊔ K₁) ⊓ K₂ with hE₂
  have hEU : E ≤ U₁ ⊔ U₂ := hO2B ▸ hEO
  have hUK : U₁ ⊔ U₂ ≤ K₁ ⊔ K₂ := sup_le_sup (stdSub_le _ _) (stdSub_le _ _)
  have hEK : E ≤ K₁ ⊔ K₂ := hEU.trans hUK
  have hUK₁ : (U₁ ⊔ U₂) ⊓ K₁ = U₁ := le_antisymm
    ((inf_le_inf_right _ (sup_le_sup_left (stdSub_le θ₂ Ū) _)).trans
      (sup_inf_eq_of_le hc hd (stdSub_le θ₁ Ū)).le) (le_inf le_sup_left (stdSub_le _ _))
  have hSK₁ : (S : Subgroup A) ⊓ K₁ = U₁ := by
    rw [← hUK₁, ← hSK, inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have hBK₁' : (stdSub θ₁ (sl2Borel k) ⊔ stdSub θ₂ (sl2Borel k)) ⊓ K₁ = stdSub θ₁ (sl2Borel k) :=
    le_antisymm ((inf_le_inf_right _ (sup_le_sup_left (stdSub_le θ₂ _) _)).trans
      (sup_inf_eq_of_le hc hd (stdSub_le θ₁ _)).le) (le_inf le_sup_left (stdSub_le _ _))
  have hBK₁ : B ⊓ K₁ = stdSub θ₁ (sl2Borel k) := by
    rw [← hBK₁', ← hBK, inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have hE₁U : E₁ ≤ U₁ := proj_le hc hd hEU (stdSub_le _ _) (stdSub_le _ _)
  have hE₂U : E₂ ≤ U₂ := by
    have := proj_le hc' (by rw [inf_comm]; exact hd) (sup_comm U₁ U₂ ▸ hEU) (stdSub_le θ₂ Ū)
      (stdSub_le θ₁ Ū)
    exact this
  have hEE : E ≤ E₁ ⊔ E₂ := le_sup_projections hc hEK
  obtain ⟨s, hsR, hs₁⟩ := hRsw
  have hs₂ : K₂.map (MulAut.conj s).toMonoidHom = K₁ := by
    obtain ⟨σ₁, σ₂, ⟨h₁, -⟩ | ⟨-, h₂⟩⟩ := hRperm s hsR
    · exfalso
      apply ne_bot_of_sl2 θ₁
      rw [← hd, ← h₁.1, hs₁, inf_idem]
    · exact h₂.1
  have hsE : s ∈ normalizer (E : Set A) := hSE (hRS hsR)
  have hE₁₂ : E₁.map (MulAut.conj s).toMonoidHom = E₂ := map_proj_of_swap hs₁ hs₂ hsE
  have hcardE : Nat.card E₁ = Nat.card E₂ := by
    rw [← hE₁₂, card_map_of_injective (f := (MulAut.conj s).toMonoidHom) (MulAut.conj s).injective]
  have hE₁2 : IsPGroup 2 E₁ := (isPGroup_stdSub_upperUnipotent hk θ₁).to_le hE₁U
  obtain ⟨r, hr⟩ := hE₁2.exists_card_eq
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      rw [h, pow_zero] at hr
      have h1 : E₁ = ⊥ := card_eq_one.1 hr
      have h2 : E₂ = ⊥ := card_eq_one.1 (hcardE ▸ hr)
      rw [h1, h2, sup_bot_eq] at hEE
      have h3 := card_le_of_le hEE
      rw [card_bot] at h3
      omega
    · exact h
  have hE₂comm : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    stdSub_upperUnipotent_comm θ₂ (hE₂U ha) (hE₂U hb)
  refine ⟨θ₁, θ₂, R, hR2, hKR, hKRt, hRperm, ⟨s, hsR, hs₁⟩, hS, hB, hEU, hSK₁, hBK₁, hE₁U,
    hE₂U, r, hr1, hr, hcardE ▸ hr, ?_⟩
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  ·
    have hr1' : r = 1 := by omega
    have hE₁c : Nat.card E₁ = 2 := by rw [hr, hr1', pow_one]
    obtain ⟨x₁, L₁, hx₁K, hL₁, hx₁L, hL₁K, hD, hBL, hSL, hsyl, hcore, hO2, hO2P⟩ :=
      paired_dihedral hSK₁ hBK₁ hE₁U hE₁c
    have hcard12 : Nat.card ↥(E₁ ⊔ E₂) = 4 := by
      rw [card_sup_of_commute (fun a ha b hb =>
          hc a ((show E₁ ≤ K₁ from inf_le_right) ha) b ((show E₂ ≤ K₂ from inf_le_right) hb))
        (eq_bot_iff.2 ((inf_le_inf inf_le_right inf_le_right).trans hd.le)), hE₁c, ← hcardE,
        hE₁c]
    have hE12 : E = E₁ ⊔ E₂ := eq_of_le_of_card_ge hEE (by rw [hcard12]; exact hE4)
    have hEc : Nat.card E = 4 := by rw [hE12, hcard12]
    have hLeq : E ⊔ conjugate E x₁ = L₁ ⊔ E₂ := by
      refine le_antisymm (hL₁ ▸ sup_conjugate_le hc hEK hx₁K) (sup_le ?_ ?_)
      · have hE₁E : E₁ ≤ E := hE12 ▸ le_sup_left
        rw [hL₁]
        exact sup_le (hE₁E.trans le_sup_left) ((map_mono hE₁E).trans le_sup_right)
      · exact (hE12 ▸ le_sup_right : E₂ ≤ E).trans le_sup_left
    exact ⟨x₁, L₁, hx₁K, hL₁, hx₁L, hL₁K, hLeq, hsyl, hcore, hO2, hO2P,
      fun h => absurd h (by omega), fun _ => ⟨hEc, hE12, hD, hBL, hSL⟩⟩
  ·
    have hE₁4 : 4 ≤ Nat.card E₁ := by
      rw [hr]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ r := Nat.pow_le_pow_right two_pos hr2
    obtain ⟨x₁, L₁, hx₁K, hL₁, hx₁L, hL₁K, hsyl, hcore, hO2, hO2P, f, hf, hfn, hEf, e, heB,
      heU⟩ := paired_high hk hSK₁ hBK₁ hE₁U hE₁4
    have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have : Group.IsPerfect (PSL2MatrixGroup (GaloisField 2 f)) := by
      rw [Group.isPerfect_def]
      have h2 : 2 < Nat.card (GaloisField 2 f) := by
        rw [hcardF]
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right two_pos hf
      exact SL2Simple.PSL_commutator_eq_top (exists_ne_zero_sq_ne_one h2)
    have : Group.IsPerfect L₁ :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hLeq : E ⊔ conjugate E x₁ = L₁ ⊔ E₂ :=
      sup_conjugate_eq_of_perfect hc hEK hx₁K hL₁ hE₂comm
    have hrf : r ≤ f := by
      have h1 : 2 ^ r ≤ 2 ^ f := hr ▸ hEf
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    exact ⟨x₁, L₁, hx₁K, hL₁, hx₁L, hL₁K, hLeq, hsyl, hcore, hO2, hO2P,
      fun _ => ⟨f, hf, hrf, hfn, e, heB, heU⟩, fun h => absurd h (by omega)⟩

end CFSG.Quasithin.H13.QRC
