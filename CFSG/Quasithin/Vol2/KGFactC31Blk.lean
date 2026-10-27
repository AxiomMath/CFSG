module

public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueHatA6
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.KGFactC31Hex

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {Γ : Type} [Group Γ]

@[expose] def NoNormalTwo (X : Type*) [Group X] : Prop :=
  ∀ K : Subgroup X, K.Normal → IsPGroup 2 ↥K → K = ⊥

theorem noNormalTwo_of_simple {X : Type*} [Group X] [hs : IsSimpleGroup X]
    (hX : ¬ IsPGroup 2 X) : NoNormalTwo X := by
  intro K hK h2
  rcases hs.eq_bot_or_eq_top_of_normal K with h | h
  · exact h
  · exfalso
    apply hX
    intro g
    obtain ⟨k, hk⟩ := h2 ⟨g, h ▸ Subgroup.mem_top g⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem noNormalTwo_of_isHat {X S : Type} [Group X] [Group S] [Finite X]
    (h : CFSG.Quasithin.IsHat X S) (hS : NoNormalTwo S) : NoNormalTwo X := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  intro K hK h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := (e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hKZ : K ≤ Subgroup.center X := by
    have h1 : K.map π = ⊥ := hS _ (hK.map π hπ) (h2.map π)
    intro k hk
    have h3 : π k ∈ K.map π := ⟨k, hk, rfl⟩
    rw [h1, Subgroup.mem_bot] at h3
    have h4 : (QuotientGroup.mk' (Subgroup.center X) k) = 1 := e.injective (by simpa [π] using h3)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  refine eq_bot_iff.mpr fun k hk => ?_
  obtain ⟨n, hn⟩ := h2 ⟨k, hk⟩
  have hk1 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hz : (⟨k, hKZ hk⟩ : ↥(Subgroup.center X)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hk1)
  have hdvd : orderOf (⟨k, hKZ hk⟩ : ↥(Subgroup.center X)) ∣ 3 := by
    rw [← hZ]
    exact orderOf_dvd_natCard _
  have hdvd2 := orderOf_dvd_of_pow_eq_one hz
  have h1 : orderOf (⟨k, hKZ hk⟩ : ↥(Subgroup.center X)) = 1 := by
    have h3 : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.eq_one_of_dvd_coprimes h3 hdvd hdvd2
  rw [orderOf_eq_one_iff] at h1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

theorem pCoreOf_eq_of_surj [Finite Γ] {L N : Subgroup Γ} (hNL : N ≤ L) (hN2 : IsPGroup 2 ↥N)
    {X : Type*} [Group X] (φ : ↥L →* X) (hφ : Function.Surjective φ)
    (hker : φ.ker = N.subgroupOf L) (hX : NoNormalTwo X) : pCoreOf 2 L = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (N.subgroupOf L).Normal := hker ▸ φ.normal_ker
  have hLN : L ≤ Subgroup.normalizer (N : Set Γ) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn'
      have := hn.conj_mem ⟨n, hNL hn'⟩ (Subgroup.mem_subgroupOf.mpr hn') ⟨l, hl⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    · intro hn'
      have hnL : n ∈ L := by
        have h1 : l * n * l⁻¹ ∈ L := hNL hn'
        have : n = l⁻¹ * (l * n * l⁻¹) * l := by group
        rw [this]
        exact L.mul_mem (L.mul_mem (L.inv_mem hl) h1) hl
      have := hn.conj_mem ⟨l * n * l⁻¹, hNL hn'⟩ (Subgroup.mem_subgroupOf.mpr hn') ⟨l, hl⟩⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      simpa [mul_assoc] using this
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 hNL hLN hN2)
  have hPn : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hP : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥L) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h1 : (CFSG.Open.pCore 2 ↥L).map φ = ⊥ := hX _ (hPn.map φ hφ) (hP.map φ)
  rintro _ ⟨p, hp, rfl⟩
  have h2 : φ p ∈ (CFSG.Open.pCore 2 ↥L).map φ := ⟨p, hp, rfl⟩
  rw [h1, Subgroup.mem_bot] at h2
  have h3 : p ∈ φ.ker := h2
  rw [hker, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem hat_autI_irr [Finite Γ] {L Q : Subgroup Γ} [(Q.subgroupOf L).Normal]
    (hQ : IsElemAbelian 2 Q) (hLN : L ≤ Subgroup.normalizer (Q : Set Γ))
    (hcard : Nat.card Q = 64) (hC : L ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q)
    (hhat : CFSG.Quasithin.IsHat (↥L ⧸ Q.subgroupOf L) ↥(alternatingGroup (Fin 6))) :
    fixV (autI hQ L) = ⊥ ∧ ∀ W : Subgroup (IntMod Q hQ),
      (∀ φ ∈ autI hQ L, ∀ w ∈ W, φ w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  have hQC : Q ≤ Subgroup.centralizer (Q : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hQab y hy x hx
  let ψ : ↥L →* MulAut (IntMod Q hQ) := (convI hQ).comp (Subgroup.inclusion hLN)
  have hψker : ψ.ker = Q.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show convI hQ (Subgroup.inclusion hLN x) = 1 ↔ _
    rw [convI_eq_one_iff]
    exact ⟨fun h => hC ⟨x.2, h⟩, fun h => hQC h⟩
  have hψrange : ψ.range = autI hQ L := by
    ext φ
    rw [MonoidHom.mem_range, mem_autI]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hLN x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  let eH : ↥L ⧸ Q.subgroupOf L ≃* ↥(autI hQ L) :=
    ((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hψrange)
  have hHhat : CFSG.Quasithin.IsHat ↥(autI hQ L) ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv eH hhat
  have hcardI : Nat.card (IntMod Q hQ) = 2 ^ 6 := by
    show Nat.card ↥Q = 2 ^ 6
    rw [hcard]; norm_num
  exact H13.hatA6SixIrreducible (IntMod Q hQ) IntMod.sq_eq_one hcardI
    (autI hQ L) hHhat.1.1 hHhat.2.1 hHhat.2.2

theorem irr_of_hat [Finite Γ] {L Q : Subgroup Γ} [(Q.subgroupOf L).Normal]
    (hQ : IsElemAbelian 2 Q) (hLN : L ≤ Subgroup.normalizer (Q : Set Γ))
    (hcard : Nat.card Q = 64) (hC : L ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q)
    (hhat : CFSG.Quasithin.IsHat (↥L ⧸ Q.subgroupOf L) ↥(alternatingGroup (Fin 6)))
    {W : Subgroup Γ} (hWQ : W ≤ Q) (hLW : L ≤ Subgroup.normalizer (W : Set Γ)) :
    W = ⊥ ∨ W = Q :=
  CFSG.Quasithin.MS93.eq_bot_or_eq_of_autI hQ (hat_autI_irr hQ hLN hcard hC hhat).2 hWQ hLW

theorem isHatA6Block_of [Finite Γ] {L Q : Subgroup Γ} [(Q.subgroupOf L).Normal]
    (hQ : IsElemAbelian 2 Q) (hQL : Q ≤ L)
    (hLN : L ≤ Subgroup.normalizer (Q : Set Γ)) (hO : pCoreOf 2 L = Q) (hcard : Nat.card Q = 64)
    (hC : L ⊓ Subgroup.centralizer (Q : Set Γ) ≤ Q) (hperf : ⁅L, L⁆ = L)
    (hhat : CFSG.Quasithin.IsHat (↥L ⧸ Q.subgroupOf L) ↥(alternatingGroup (Fin 6))) :
    CFSG.Quasithin.IsHatA6Block L := by
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  have hQC : Q ≤ Subgroup.centralizer (Q : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hQab y hy x hx
  obtain ⟨hfix, hirr⟩ := hat_autI_irr hQ hLN hcard hC hhat
  have hinf : Q ⊓ Subgroup.centralizer (L : Set Γ) = ⊥ := by
    refine eq_bot_iff.mpr fun v ⟨hvQ, hvC⟩ => ?_
    have hmem : IntMod.mk hQ ⟨v, hvQ⟩ ∈ fixV (autI hQ L) := by
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_autI hQ).1 hφ
      apply IntMod.val_injective
      rw [convI_apply_val]
      show (g : Γ) * v * (g : Γ)⁻¹ = v
      rw [Subgroup.mem_centralizer_iff.mp hvC g hg, mul_inv_cancel_right]
    rw [hfix, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrArg IntMod.val hmem
  have hcommle : ⁅Q, L⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    rw [commutatorElement_def]
    have h1 : l * q⁻¹ * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLN hl) _).mp (Q.inv_mem hq)
    have := Q.mul_mem hq h1
    rwa [show q * (l * q⁻¹ * l⁻¹) = q * l * q⁻¹ * l⁻¹ by group] at this
  have hcommN : L ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup Γ) : Set Γ) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := Q) (H₂ := L)
  have hU : ⁅Q, L⁆ = Q := by
    rcases CFSG.Quasithin.MS93.eq_bot_or_eq_of_autI hQ hirr hcommle hcommN with h | h
    · exfalso
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      have hLQ : L ≤ Q := fun l hl => hC ⟨hl, Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_iff.mp (h hq) l hl).symm⟩
      have hall : ∀ x : ↥L ⧸ Q.subgroupOf L, x = 1 := by
        intro x
        induction x using QuotientGroup.induction_on with
        | H g => rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact hLQ g.2
      obtain ⟨⟨-, -, a, b, hab⟩, -, -⟩ := hhat
      apply hab
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b => rw [hall a, hall b]
    · exact h
  have hbQ : blockQ L = Q := hO
  have hbU : blockU L = Q := by rw [blockU, hbQ, hU]
  have hbZ : blockZ L = ⊥ := by rw [blockZ, hbU, hinf]
  have hpk : CFSG.pCore 2 ↥L = Q.subgroupOf L := by rw [← Hex.pCoreOf_subgroupOf' L, hO]
  have hhatP : CFSG.Quasithin.IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpk).symm hhat
  have hpL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hshort : IsShort2 L := by
    refine ⟨fun N _ hN => Hex.eq_top_of_isPGroup_quot' N hN, ?_, ⟨?_, ?_⟩, Or.inl hhatP.1,
      ?_, ?_⟩
    · unfold CharTwo
      rw [hO]
      exact hC
    · rw [hbU, hbQ]
      exact le_inf le_rfl hQC
    · intro x hx
      rw [hbU] at hx
      exact hQ.2 x hx
    · rw [hbZ, hbU]
      exact bot_lt_iff_ne_bot.mpr hQne
    · intro W hZW hWU hLW
      rw [hbZ, hbU] at *
      exact CFSG.Quasithin.MS93.eq_bot_or_eq_of_autI hQ hirr hWU hLW
  refine ⟨hshort, hhatP, ?_, ?_⟩
  · rw [hbU, hcard]
    norm_num
  · rw [hbU, hO]
    exact le_antisymm hC (le_inf hQL hQC)

end CFSG.Quasithin.KGC31

end
