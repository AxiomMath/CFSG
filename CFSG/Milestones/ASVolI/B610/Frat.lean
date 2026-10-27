module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

universe u

theorem burnsideB610_exists_complement_aux {X : Type*} [Group X] [Finite X] {K N M : Subgroup X}
    [K.Normal] [N.Normal] (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNK : N ≤ K)
    (hM : IsMaxSubgroupIn K M) (hcore : (M ⊓ N).normalCore = ⊥) (n : ℕ) :
    ∀ C : Subgroup X, Nat.card ↥(N ⊓ C) = n → C ≤ K → N ⊔ C = K →
      ∃ C' : Subgroup X, C' ≤ C ∧ N ⊓ C' = ⊥ ∧ N ⊔ C' = K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C hn hCK hsup
  by_cases hA : N ⊓ C = ⊥
  · exact ⟨C, le_rfl, hA, hsup⟩
  obtain ⟨g, hg⟩ : ∃ g : X, ¬ N ⊓ C ≤ conjSub g M := by
    by_contra hcon
    push Not at hcon
    apply hA
    rw [eq_bot_iff, ← hcore]
    intro a ha b
    refine ⟨?_, ‹N.Normal›.conj_mem a ha.1 b⟩
    have h1 := hcon b⁻¹ ha
    rw [mem_conjSub, inv_inv] at h1
    exact h1
  have hgK : g ∈ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normalizer_eq_top_iff.mpr ‹K.Normal›).ge (Subgroup.mem_top g)
  have hM' : IsMaxSubgroupIn K (conjSub g M) := by
    have h1 := (isMaxSubgroupIn_conjSub (g := g)).mpr hM
    rwa [conjSub_eq_self hgK] at h1
  have hAnorm : K ≤ Subgroup.normalizer ((N ⊓ C : Subgroup X) : Set X) := by
    rw [← hsup]
    refine sup_le (fun n hn => ?_) (fun c hc => ?_)
    · refine mem_normalizer_of_forall_mem (fun a ha => ?_) (fun a ha => ?_)
      · have h1 : n * a * n⁻¹ = a := by rw [hN n hn a ha.1, mul_inv_cancel_right]
        rw [h1]
        exact ha
      · have h1 : n⁻¹ * a * n = a := by
          rw [hN n⁻¹ (N.inv_mem hn) a ha.1, inv_mul_cancel_right]
        rw [h1]
        exact ha
    · have hcN : c ∈ Subgroup.normalizer (N : Set X) :=
        (Subgroup.normalizer_eq_top_iff.mpr ‹N.Normal›).ge (Subgroup.mem_top c)
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcN, Subgroup.le_normalizer hc⟩
  have hMA : conjSub g M ⊔ (N ⊓ C) = K := by
    refine hM'.2 _ (lt_of_le_of_ne le_sup_left fun heq => hg ?_)
      (sup_le hM'.le (inf_le_right.trans hCK))
    rw [heq]
    exact le_sup_right
  have hsup₁ : N ⊔ (C ⊓ conjSub g M) = K := by
    refine le_antisymm (sup_le hNK (inf_le_left.trans hCK)) fun x hx => ?_
    rw [← hsup] at hx
    have hx' : x ∈ ((N ⊔ C : Subgroup X) : Set X) := hx
    rw [Subgroup.normal_mul] at hx'
    obtain ⟨m, hm, c, hc, rfl⟩ := Set.mem_mul.mp hx'
    have hcK : c ∈ ((conjSub g M ⊔ (N ⊓ C) : Subgroup X) : Set X) := by
      rw [hMA]
      exact hCK hc
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hM'.le.trans hAnorm)] at hcK
    obtain ⟨k, hk, a, ha, rfl⟩ := Set.mem_mul.mp hcK
    have hkC : k ∈ C := by
      have h1 := C.mul_mem hc (C.inv_mem ha.2)
      rwa [mul_inv_cancel_right] at h1
    rw [← mul_assoc]
    exact (N ⊔ (C ⊓ conjSub g M)).mul_mem
      ((N ⊔ (C ⊓ conjSub g M)).mul_mem (Subgroup.mem_sup_left hm)
        (Subgroup.mem_sup_right ⟨hkC, hk⟩)) (Subgroup.mem_sup_left ha.1)
  have hlt : N ⊓ (C ⊓ conjSub g M) < N ⊓ C := by
    refine lt_of_le_of_ne (inf_le_inf_left N inf_le_left) fun heq => hg ?_
    rw [← heq]
    exact inf_le_right.trans inf_le_right
  obtain ⟨C', hC', hbot, hsup'⟩ := ih _ (hn ▸ Subgroup.card_lt_of_lt hlt) (C ⊓ conjSub g M) rfl
    (inf_le_left.trans hCK) hsup₁
  exact ⟨C', hC'.trans inf_le_left, hbot, hsup'⟩

theorem burnsideB610_exists_complement {X : Type*} [Group X] [Finite X] {K N M : Subgroup X}
    [K.Normal] [N.Normal] (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNK : N ≤ K)
    (hM : IsMaxSubgroupIn K M) (hcore : (M ⊓ N).normalCore = ⊥) :
    ∃ C : Subgroup X, N ⊓ C = ⊥ ∧ N ⊔ C = K := by
  obtain ⟨C, -, h1, h2⟩ := burnsideB610_exists_complement_aux hN hNK hM hcore _ K rfl le_rfl
    (sup_eq_right.mpr hNK)
  exact ⟨C, h1, h2⟩

theorem burnsideB610_isMaxSubgroupIn_map {X Y : Type*} [Group X] [Group Y] {φ : X →* Y}
    (hφ : Function.Surjective φ) {K M : Subgroup X} (hker : φ.ker ≤ M)
    (hM : IsMaxSubgroupIn K M) : IsMaxSubgroupIn (K.map φ) (M.map φ) := by
  have hMK : M ≤ K := hM.le
  refine ⟨lt_of_le_of_ne (Subgroup.map_mono hMK) fun heq => ?_, fun L hL hLK => ?_⟩
  · have h1 : (M.map φ).comap φ = (K.map φ).comap φ := by rw [heq]
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_eq_left.mpr hker,
      sup_eq_left.mpr (hker.trans hMK)] at h1
    exact (ne_of_lt hM.1) h1
  · have hLc : L.comap φ ≤ K := by
      have h1 : L.comap φ ≤ (K.map φ).comap φ := Subgroup.comap_mono hLK
      rwa [Subgroup.comap_map_eq, sup_eq_left.mpr (hker.trans hMK)] at h1
    have hML : M < L.comap φ := by
      refine lt_of_le_of_ne (Subgroup.map_le_iff_le_comap.mp hL.le) fun heq => ?_
      apply ne_of_lt hL
      rw [heq, Subgroup.map_comap_eq_self_of_surjective hφ]
    have h1 := hM.2 _ hML hLc
    rw [← Subgroup.map_comap_eq_self_of_surjective hφ L, h1]

theorem burnsideB610_le_of_isMaxSubgroupIn_aux (n : ℕ) :
    ∀ (X : Type u) [Group X] [Finite X], Nat.card X = n →
      ∀ K D : Subgroup X, K.Normal → D.Normal → (∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ K) → D ≤ K →
        ¬ 2 ∣ Nat.card D → D ≤ frattini X → ∀ M : Subgroup X, IsMaxSubgroupIn K M → D ≤ M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn K D hKn hDn hK2 hDK hDodd hDΦ M hM
  by_contra hDM
  by_cases hcore : (M ⊓ D).normalCore = ⊥
  ·
    have hDne : D ≠ ⊥ := fun h => hDM (h ▸ bot_le)
    have : Group.IsNilpotent (frattini X) := frattini_nilpotent
    have : Group.IsNilpotent D := Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDΦ)
    have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
    set Z := (Subgroup.center D).map D.subtype with hZ
    have hZD : Z ≤ D := Subgroup.map_subtype_le _
    have hZne : Z ≠ ⊥ := by
      intro h
      apply Group.IsNilpotent.center_ne_bot D
      rw [eq_bot_iff]
      intro z hz
      have h1 : (z : X) ∈ Z := ⟨z, hz, rfl⟩
      rw [h] at h1
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))
    have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
      rintro _ ⟨a, -, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hb a)
    have hZcore : (M ⊓ Z).normalCore = ⊥ := by
      rw [eq_bot_iff, ← hcore]
      exact Subgroup.normalCore_mono (inf_le_inf_left M hZD)
    obtain ⟨C, hZC, hZCK⟩ := burnsideB610_exists_complement hZcomm (hZD.trans hDK) hM hZcore
    have : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext (hZcomm a a.2 b b.2)⟩⟩
    have hcop : Nat.Coprime K.index (Nat.card Z) := by
      obtain ⟨m, hm⟩ := exists_relIndex_eq_two_pow (D := ⊤)
        (Subgroup.normalizer_eq_top_iff.mpr hKn).ge (fun x _ => hK2 x)
      rw [Subgroup.relIndex_top_right] at hm
      rw [hm]
      refine Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      exact fun h2 => hDodd (h2.trans (Subgroup.card_dvd_of_le hZD))
    obtain ⟨D', -, hZD'1, hZD'2⟩ :=
      CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting Z K C hcop hZC hZCK
    have hD'top : D' = ⊤ := by
      apply frattini_nongenerating
      rw [eq_top_iff, ← hZD'2]
      exact sup_le (le_sup_of_le_right (hZD.trans hDΦ)) le_sup_left
    apply hZne
    rw [← hZD'1, hD'top, inf_top_eq]
  ·
    set N₀ := (M ⊓ D).normalCore with hN₀
    set φ := QuotientGroup.mk' N₀ with hφ
    have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective N₀
    have hker : φ.ker = N₀ := QuotientGroup.ker_mk' N₀
    have hN₀M : N₀ ≤ M := (Subgroup.normalCore_le _).trans inf_le_left
    have hlt : Nat.card (X ⧸ N₀) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup N₀]
      have h1 : 1 < Nat.card N₀ := (Subgroup.one_lt_card_iff_ne_bot N₀).mpr hcore
      have h0 : 0 < Nat.card (X ⧸ N₀) := Nat.card_pos
      exact lt_mul_of_one_lt_right h0 h1
    have key := ih _ hlt (X ⧸ N₀) rfl (K.map φ) (D.map φ) (hKn.map φ hφs) (hDn.map φ hφs)
      (fun y => by
        obtain ⟨x, rfl⟩ := hφs y
        obtain ⟨k, hk⟩ := hK2 x
        exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map_of_mem φ hk⟩)
      (Subgroup.map_mono hDK)
      (fun h2 => hDodd (h2.trans (Subgroup.card_map_dvd D φ)))
      (Subgroup.map_le_iff_le_comap.mpr (hDΦ.trans (frattini_le_comap_frattini_of_surjective hφs)))
      (M.map φ) (burnsideB610_isMaxSubgroupIn_map hφs (hker.le.trans hN₀M) hM)
    apply hDM
    have h1 := Subgroup.map_le_iff_le_comap.mp key
    rwa [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hN₀M] at h1

theorem burnsideB610_le_frattini_of_normal {X : Type*} [Group X] [Finite X] {K D : Subgroup X}
    [K.Normal] [D.Normal] (hK2 : ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ K) (hDK : D ≤ K)
    (hDodd : ¬ 2 ∣ Nat.card D) (hDΦ : D ≤ frattini X) : D.subgroupOf K ≤ frattini K := by
  unfold frattini Order.radical
  refine le_iInf₂ fun M' hM' => ?_
  have hM : IsMaxSubgroupIn K (M'.map K.subtype) :=
    isMaxSubgroupIn_map_subtype (isMaxSubgroupIn_top_iff.mpr hM')
  have h := burnsideB610_le_of_isMaxSubgroupIn_aux _ X rfl K D ‹_› ‹_› hK2 hDK hDodd hDΦ _ hM
  intro x hx
  obtain ⟨y, hy, hyx⟩ := h (Subgroup.mem_subgroupOf.mp hx)
  rwa [Subtype.ext hyx] at hy

theorem burnsideB610_twoResidual_le_sup_pCore {X : Type*} [Group X] [Finite X] {T M : Subgroup X}
    (h : MinParabolic (⊤ : Subgroup X) T M) {Y : Subgroup X}
    (hY : twoResidual (⊤ : Subgroup X) ≤ Y ⊔ kerIn M ⊤) :
    twoResidual (⊤ : Subgroup X) ≤ Y ⊔ CFSG.Open.pCore 2 X := by
  set Q := CFSG.Open.pCore 2 X with hQ
  set φ := QuotientGroup.mk' Q with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  have hker : φ.ker ≤ M := by
    rw [hφ, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  set P := twoResidual (⊤ : Subgroup (X ⧸ Q)) with hP
  have hPn : P.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hJbar : (kerIn M ⊤).map φ = frattini (X ⧸ Q) := h.map_kerIn_eq_frattini
  have hKmap : (twoResidual (⊤ : Subgroup X)).map φ = P := twoResidual_map_top hφs
  have hΦodd : ¬ 2 ∣ Nat.card (frattini (X ⧸ Q)) := by
    have h1 := (h.map_of_surjective hφs hker).card_kerIn_odd pCore_quotient_pCore
    rwa [kerIn_map_top hφs hker, hJbar] at h1
  have hΦP : frattini (X ⧸ Q) ≤ P :=
    le_twoResidual_of_odd (Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact hΦodd))
  have hP2 : ∀ y : X ⧸ Q, ∃ k : ℕ, y ^ 2 ^ k ∈ P := fun y =>
    twoResidual_isTwoQuotient ⊤ y (Subgroup.mem_top y)
  have hfr : (frattini (X ⧸ Q)).subgroupOf P ≤ frattini P :=
    burnsideB610_le_frattini_of_normal hP2 hΦP hΦodd le_rfl
  have h1 : P ≤ Y.map φ ⊔ frattini (X ⧸ Q) :=
    calc P = (twoResidual (⊤ : Subgroup X)).map φ := hKmap.symm
      _ ≤ (Y ⊔ kerIn M ⊤).map φ := Subgroup.map_mono hY
      _ = Y.map φ ⊔ (kerIn M ⊤).map φ := Subgroup.map_sup _ _ _
      _ = Y.map φ ⊔ frattini (X ⧸ Q) := by rw [hJbar]
  have h2 : P ≤ Y.map φ := by
    have h3 : (Y.map φ).subgroupOf P ⊔ frattini P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, f, hf, hyf⟩ := Subgroup.mem_sup_of_normal_right.mp (h1 x.2)
      have hfP : f ∈ P := hΦP hf
      have hyP : y ∈ P := by
        have : y = (x : X ⧸ Q) * f⁻¹ := by rw [← hyf, mul_inv_cancel_right]
        rw [this]
        exact P.mul_mem x.2 (P.inv_mem hfP)
      have hx : x = ⟨y, hyP⟩ * ⟨f, hfP⟩ := Subtype.ext (by simpa using hyf.symm)
      rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hy))
        (Subgroup.mem_sup_right (hfr (Subgroup.mem_subgroupOf.mpr hf)))
    have h4 := frattini_nongenerating h3
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ (Y.map φ).subgroupOf P := by rw [h4]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  calc twoResidual (⊤ : Subgroup X) ≤ (Y.map φ).comap φ := by
        rw [← Subgroup.map_le_iff_le_comap, hKmap]
        exact h2
    _ = Y ⊔ Q := by rw [Subgroup.comap_map_eq, hφ, QuotientGroup.ker_mk']

theorem burnsideB610_twoResidual_le_sup_pCoreOf {G : Type*} [Group G] [Finite G]
    {H T M : Subgroup G} (h : MinParabolic H T M) {Y : Subgroup G} (hYH : Y ≤ H)
    (hY : twoResidual H ≤ Y ⊔ kerIn M H) : twoResidual H ≤ Y ⊔ pCoreOf 2 H := by
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hJH : kerIn M H ≤ H := h.kerIn_le_H
  have hY' : twoResidual (⊤ : Subgroup H) ≤
      Y.subgroupOf H ⊔ kerIn (M.subgroupOf H) ⊤ := by
    rw [B6.twoResidual_top_eq_subgroupOf, B6.kerIn_subgroupOf_top,
      ← Subgroup.map_le_map_iff_of_injective H.subtype_injective, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hKH, Subgroup.map_subgroupOf_eq_of_le hYH,
      Subgroup.map_subgroupOf_eq_of_le hJH]
    exact hY
  have h1 := burnsideB610_twoResidual_le_sup_pCore h.subgroupOf hY'
  rw [B6.twoResidual_top_eq_subgroupOf,
    ← Subgroup.map_le_map_iff_of_injective H.subtype_injective, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hKH, Subgroup.map_subgroupOf_eq_of_le hYH] at h1
  exact h1

end CFSG.Quasithin
