module

public import CFSG.Quasithin.Background.F918C3

public section

namespace CFSG.Quasithin.H13.KGFFZ

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SectionFaithful (T V₁ Vp H K : Subgroup G) : Prop :=
  ∀ F E : Subgroup G, V₁ ≤ F → F ≤ E → E ≤ conjClosure Vp H →
    conjClosure K T ⊔ T ≤ Subgroup.normalizer (F : Set G) →
    conjClosure K T ⊔ T ≤ Subgroup.normalizer (E : Set G) →
    (¬ ∀ k ∈ conjClosure K T, ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ F) →
    ∀ x ∈ conjClosure K T,
      (∀ k' ∈ conjClosure K T, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) →
      (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) → x ∈ pCoreOf 2 H

section F918

open CFSG.Quasithin.HypF918

variable {T V L V₁ Vp H K : Subgroup G}

theorem ker_le_pCoreOf' (h : HypF918 T V L V₁ Vp H K) (hH : H = conjClosure K T ⊔ T)
    {F E : Subgroup G} (hF : conjClosure K T ⊔ T ≤ Subgroup.normalizer (F : Set G))
    (hE : conjClosure K T ⊔ T ≤ Subgroup.normalizer (E : Set G))
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ F)
    (hQ : ∀ q ∈ pCoreOf 2 H, ∀ e ∈ E, q * e * q⁻¹ * e⁻¹ ∈ F)
    (hZE : ∀ x ∈ conjClosure K T,
      (∀ k' ∈ conjClosure K T, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) →
      (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) → x ∈ pCoreOf 2 H) :
    ∀ x ∈ conjClosure K T ⊔ T, (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) → x ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hXH : conjClosure K T ⊔ T ≤ H := h.K₀T_le_H
  have hHX : H ≤ conjClosure K T ⊔ T := hH.le
  have hXn : conjClosure K T ⊔ T ≤
      Subgroup.normalizer ((conjClosure K T ⊔ T : Subgroup G) : Set G) := Subgroup.le_normalizer
  have hK₀n : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    K₀T_le_normalizer_K₀ T K
  set Nx := centralizerMod F (conjClosure K T ⊔ T) E with hNxdef
  have hNxX : Nx ≤ conjClosure K T ⊔ T := centralizerMod_le_left _ _ _
  have hNxn : conjClosure K T ⊔ T ≤ Subgroup.normalizer (Nx : Set G) :=
    le_normalizer_centralizerMod hF hXn hE
  have hNx3 : ∀ x ∈ conjClosure K T ⊔ T, (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) → x ∈ Nx :=
    fun x hx hxE => ⟨hx, hF hx, hxE⟩
  have hNx4 : ∀ n ∈ Nx, ∀ e ∈ E, n * e * n⁻¹ * e⁻¹ ∈ F := fun n hn e he => hn.2.2 e he
  have hQNx : pCoreOf 2 H ≤ Nx := fun q hq =>
    hNx3 q (hHX (pCoreOf_le 2 H hq)) (hQ q hq)
  have hDK₀ : ⁅Nx, conjClosure K T⁆ ≤ conjClosure K T :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hNxX.trans hK₀n)
  have hDNx : ⁅Nx, conjClosure K T⁆ ≤ Nx := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hNxn)
  have hDn : conjClosure K T ⊔ T ≤
      Subgroup.normalizer ((⁅Nx, conjClosure K T⁆ : Subgroup G) : Set G) :=
    F9.le_normalizer_commutator_of_le hNxn hK₀n
  have hDQ : ⁅Nx, conjClosure K T⁆ ≤ pCoreOf 2 H := by
    rcases exists_le_or_commutator_le_pCoreOf h.K_cComp h.T_le_H h.K_quasisimple hDK₀
        (le_sup_left.trans hDn) (le_sup_right.trans hDn) with hle | hcomm
    · exact absurd (fun k hk e he => hNx4 _ (hDNx (hle hk)) e he) hnt
    · intro d hd
      exact hZE d (hDK₀ hd) (fun k' hk' => hcomm (Subgroup.commutator_mem_commutator hd hk'))
        (hNx4 d (hDNx hd))
  have hNxH : Nx ≤ H := hNxX.trans hXH
  have hK₀quot : ∀ y ∈ conjClosure K T ⊔ T, ∃ m : ℕ, y ^ 2 ^ m ∈ conjClosure K T := by
    intro y hy
    have hTn : T ≤ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T
    have hmul' : (T : Set G) * (conjClosure K T : Set G) = ↑(T ⊔ conjClosure K T) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right T (conjClosure K T) hTn).symm
    have hy' : y ∈ (T : Set G) * (conjClosure K T : Set G) := by
      rw [hmul', sup_comm]; exact hy
    obtain ⟨t, ht, a, ha, rfl⟩ := hy'
    obtain ⟨m, hm⟩ := h.sylow_H.2.1 ⟨t, ht⟩
    have hm' : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have key : ∀ n : ℕ, ∃ a' ∈ conjClosure K T, (t * a) ^ n = t ^ n * a' := by
      intro n
      induction n with
      | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
      | succ n ih =>
        obtain ⟨a', ha', h'⟩ := ih
        refine ⟨(t⁻¹ * a' * t) * a, (conjClosure K T).mul_mem
          ((Subgroup.mem_normalizer_iff''.mp (hTn ht) a').mp ha') ha, ?_⟩
        rw [pow_succ, h']
        group
    obtain ⟨a', ha', h'⟩ := key (2 ^ m)
    exact ⟨m, by rw [h', hm', one_mul]; exact ha'⟩
  have hNxK : ∀ n ∈ Nx, ∀ k ∈ conjClosure K T, n * k * n⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    fun n hn k hk => hDQ (Subgroup.commutator_mem_commutator hn hk)
  have hNx2 : IsPGroup 2 ↥Nx := fun y => by
    obtain ⟨m, hm⟩ := hK₀quot y.1 (hNxX y.2)
    have hym : y.1 ^ 2 ^ m ∈ Nx := Nx.pow_mem y.2 _
    have hz : y.1 ^ 2 ^ m ∈ pCoreOf 2 H :=
      hZE _ hm (fun k' hk' => hNxK _ hym k' hk') (hNx4 _ hym)
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hz⟩
    refine ⟨m + j, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  have hNxn' : H ≤ Subgroup.normalizer (Nx : Set G) := hHX.trans hNxn
  have hNxQ : Nx ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hNxH hNxn' hNx2
  intro x hx hxE
  exact hNxQ (hNx3 x hx hxE)

theorem F918_7'' (h : HypF918 T V L V₁ Vp H K) (hH : H = conjClosure K T ⊔ T)
    (hZ : SectionFaithful T V₁ Vp H K)
    {I : Subgroup G} (hI₁ : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hI : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H)) :
    tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ := by
  have h1 := h.toHypF98.toHypF91
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    h.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le h.toHypF98.F911_3 hIHU
  have hQV₁ : ∀ x ∈ pCoreOf 2 H, ∀ e ∈ conjClosure Vp H, x * e * x⁻¹ * e⁻¹ ∈ V₁ := by
    intro x hx e he
    have := V₁.inv_mem (h1.commutator_conjClosure_le e he x hx)
    have e' : (e * x * e⁻¹ * x⁻¹)⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rwa [e'] at this
  have hWK := h.tilde_commutator_conjClosure hIU hI
  have hW0 : tildeOf V₁ (conjClosure I H) ≠ ⊥ := by
    intro hbot
    have hIV₁ : I ≤ V₁ := by
      intro i hi
      have hiN : i ∈ Subgroup.normalizer (V₁ : Set G) := h1.H_normalizes_V₁ (hUH (hIU hi))
      have : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ ∈
          tildeOf V₁ (conjClosure I H) :=
        secMk_mem_secImg (x := ⟨i, hiN⟩) (le_conjClosure I H hi)
      rw [hbot] at this
      have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ = 1 := this
      exact secMk_eq_one_iff.mp h2
    have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
      intro i hi
      refine ⟨hi, h1.H_normalizes_V₁ (hUH (hIU hi)), fun k hk => ?_⟩
      have h3 : k * i⁻¹ * k⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (h1.H_normalizes_V₁ (h.K₀_le_H hk)) i⁻¹).mp
          (V₁.inv_mem (hIV₁ hi))
      have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
      rw [e]
      exact V₁.mul_mem (hIV₁ hi) h3
    exact (not_le_of_gt hI.2.2.1) hIC
  by_contra hne
  have hnt1 : ¬ ∀ k ∈ conjClosure K T, ∀ w ∈ conjClosure I H, k * w * k⁻¹ * w⁻¹ ∈ V₁ := by
    intro hall
    have hle : ⁅conjClosure I H, conjClosure K T⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun w hw k hk => ?_
      have := V₁.inv_mem (hall k hk w hw)
      have e : (k * w * k⁻¹ * w⁻¹)⁻¹ = w * k * w⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hW0
    rw [← hWK]
    exact tildeOf_eq_bot_of_le hle
  have hnt2 : ¬ ∀ k ∈ conjClosure K T, ∀ u ∈ conjClosure Vp H,
      k * u * k⁻¹ * u⁻¹ ∈ conjClosure I H := by
    intro hall
    have hle : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ conjClosure I H := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have := (conjClosure I H).inv_mem (hall k hk u hu)
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hne
    refine le_antisymm ?_ (secImg_mono hle)
    rw [← hWK]
    exact secImg_mono (Subgroup.commutator_mono hIHU le_rfl)
  have hker1 := ker_le_pCoreOf' h hH h.K₀T_le_normalizer_V₁ hIHN hnt1
    (fun x hx e he => hQV₁ x hx e (hIHU he))
    (hZ V₁ (conjClosure I H) le_rfl (hI₁.trans (le_conjClosure I H)) hIHU
      h.K₀T_le_normalizer_V₁ hIHN hnt1)
  have hker2 := ker_le_pCoreOf' h hH hIHN h.K₀T_le_normalizer_U hnt2
    (fun x hx e he => le_conjClosure I H (hI₁ (hQV₁ x hx e he)))
    (hZ (conjClosure I H) (conjClosure Vp H) (hI₁.trans (le_conjClosure I H)) hIHU le_rfl
      hIHN h.K₀T_le_normalizer_U hnt2)
  have hFF1 : ∀ hFF : IsFFInt (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure I H))
      (h.isElemAbelian_tilde_of_le hIHU), False := fun hFF =>
    not_hasNoFaithfulFFModulesMod_of_isFFInt (F := V₁) (E := conjClosure I H)
      h.K₀T_le_normalizer_V₁ hIHN (hIHU.trans (hUH.trans h1.H_normalizes_V₁))
      (h.isElemAbelian_tilde_of_le hIHU) (fun x hx e he => hQV₁ x hx.2 e (hIHU he))
      hker1 hFF hNo
  have hFF2 : ∀ hFF : IsFFInt
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure Vp H)) (h.isElemAbelian_quotient (conjClosure I H)), False := fun hFF =>
    not_hasNoFaithfulFFModulesMod_of_isFFInt (F := conjClosure I H) (E := conjClosure Vp H) hIHN
      h.K₀T_le_normalizer_U hUW (h.isElemAbelian_quotient _)
      (fun x hx e he => le_conjClosure I H (hI₁ (hQV₁ x hx.2 e he))) hker2 hFF hNo
  rcases h.F918_6 (le_trans hI₁ (le_conjClosure I H)) hIHU hIHN hW0 hWK with ha | ⟨hb1, hb2⟩ | hc
  · exact hne ha
  · exact (hFF1 hb1).elim
  · rcases hc with hc | hc
    · exact (hFF1 (F9.IsStrongFFInt.isFFInt hc)).elim
    · exact (hFF2 (F9.IsStrongFFInt.isFFInt hc)).elim

end F918

end CFSG.Quasithin.H13.KGFFZ
