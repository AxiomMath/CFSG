module

public import CFSG.Quasithin.Background.B69Struct
public import CFSG.Quasithin.Background.B2FactorizationBlocks
public import CFSG.Quasithin.Background.FFC4NatS3
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def StructConcl (X T M : Subgroup (MulAut V)) (𝓗 : Finset (Subgroup (MulAut V))) : Prop :=
  (∀ H ∈ 𝓗, H ≤ X) ∧ ffJ X = ⨆ H ∈ 𝓗, H ∧
  (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a) ∧
  (∀ H ∈ 𝓗, H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H' = ⊥) ∧
  commV (ffJ X) ⊔ fixV (ffJ X) = (⨆ H ∈ 𝓗, commV H) ⊔ fixV (ffJ X) ∧
  (∀ H ∈ 𝓗, (commV H ⊔ fixV (ffJ X)) ⊓
      ((⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commV H') ⊔ fixV (ffJ X)) = fixV (ffJ X)) ∧
  (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → commSub (commV H) H' = ⊥) ∧
  (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, ∃ t ∈ T, B6.conjSub t H = H') ∧
  X = ffJ X ⊔ T ∧
  ∀ H ∈ 𝓗,
    (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL H (commV H) (commV H ⊓ fixV (ffJ X)) 2 e ∧
      M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V))) ∨
    (∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥H,
      (FFModel.symDn (2 * k + 1)).RealizesVia H (commV H) ⊥ π ∧
      (M ⊓ H).subgroupOf H =
        (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1))) (⟨0, by omega⟩ : Fin (2 * k + 1))).map π)

theorem b69Struct_iff : B69Struct ↔
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M : Subgroup (MulAut V)),
        (∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
          CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f) →
        MinParabolic X T M → pCoreOf 2 X = ⊥ → IsFFModule X →
        ∃ 𝓗 : Finset (Subgroup (MulAut V)), StructConcl X T M 𝓗 := Iff.rfl

section Solv

variable {X T M : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

omit [Finite V] in
theorem commV_iSup_eq {J : Subgroup (MulAut V)} (hb : IsTransvectionBlocks J 𝓗) :
    commV J = ⨆ H ∈ 𝓗, commV H := by
  rw [← hb.iSup_eq]
  simp only [commV_eq_commSub]
  apply le_antisymm
  · exact B1.commSub_biSup_le 𝓗 (fun H => H) _ fun H hH =>
      le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) =>
        commSub (⊤ : Subgroup V) K) H hH le_rfl
  · exact iSup₂_le fun H hH => commSub_mono le_rfl
      (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) H hH le_rfl)

theorem commSub_sup_fixV_inf (hV : ∀ v : V, v ^ 2 = 1) {J : Subgroup (MulAut V)}
    (hb : IsTransvectionBlocks J 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    (commV H ⊔ fixV J) ⊓ ((⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commV H') ⊔ fixV J) = fixV J := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 hx1
    obtain ⟨b, hb', c', hc', hbc⟩ := Subgroup.mem_sup.1 hx2
    have hbfix : b ∈ fixV H := by
      have hle : (⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commV H') ≤ fixV H := by
        refine iSup₂_le fun H' hH' => iSup_le fun hne u hu g hg => ?_
        rw [commV_eq_commSub] at hu
        exact hb.triv H hH H' hH' (Ne.symm hne) g hg u hu
      exact hle hb'
    have hcfix : ∀ y ∈ fixV J, y ∈ fixV H := fun y hy g hg =>
      hy g ((hb.le_J hH) hg)
    have hafix : a ∈ fixV H := by
      intro g hg
      have e : a * c = b * c' := hbc.symm
      have h1 : g (a * c) = a * c := by
        rw [e, map_mul, hbfix g hg, hcfix c' hc' g hg]
      rw [map_mul, hcfix c hc g hg] at h1
      exact mul_right_cancel h1
    have ha1 : a = 1 := by
      have : a ∈ fixV H ⊓ commSub (⊤ : Subgroup V) H :=
        ⟨hafix, by rwa [commV_eq_commSub] at ha⟩
      rw [IsTransvectionBlocks.fixV_inf_commSub hV hb hH, Subgroup.mem_bot] at this
      exact this
    rw [ha1, one_mul]
    exact hc
  · exact le_inf le_sup_right le_sup_right

omit [Finite V] in
theorem conjAut_eq_conjSub (g : MulAut V) (A : Subgroup (MulAut V)) :
    B1.conjAut g A = B6.conjSub g A :=
  Subgroup.ext fun x => by rw [B1.mem_conjAut, B6.mem_conjSub]

omit [Finite V] in
theorem le_normalizer_of_blocks {J : Subgroup (MulAut V)} (hb : IsTransvectionBlocks J 𝓗)
    {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) : J ≤ Subgroup.normalizer (H : Set (MulAut V)) := by
  rw [← hb.iSup_eq]
  refine iSup₂_le fun H' hH' => ?_
  by_cases hne : H' = H
  · subst hne
    exact Subgroup.le_normalizer
  · intro g hg
    apply mem_normalizer_of_forall_mem
    · intro x hx
      have := hb.comm H' hH' H hH hne g hg x hx
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro x hx
      have := hb.comm H' hH' H hH hne g⁻¹ (H'.inv_mem hg) x hx
      rw [this, mul_assoc, inv_mul_cancel, mul_one]
      exact hx

theorem conjSub_mem_of_blocks (hV : ∀ v : V, v ^ 2 = 1)
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    (hffJ : ffJ X = ⨆ H ∈ 𝓗, H) {g : MulAut V} (hg : g ∈ X) {L : Subgroup (MulAut V)}
    (hL : L ∈ 𝓗) : B6.conjSub g L ∈ 𝓗 := by
  have hXN : B6.conjSub g (⨆ H ∈ 𝓗, H) ≤ ⨆ H ∈ 𝓗, H := by
    intro x hx
    rw [← hffJ] at hx ⊢
    rw [B6.mem_conjSub] at hx
    have hgi := B6.le_normalizer_ffJ X (X.inv_mem hg)
    exact (Subgroup.mem_normalizer_iff.mp hgi x).mpr (by simpa using hx)
  have := hb.conjAut_mem hV (Finset.Subset.refl 𝓗) hg
    (by rw [conjAut_eq_conjSub]; exact hXN) hL
  rwa [conjAut_eq_conjSub] at this

theorem exists_conjSub_of_blocks (hV : ∀ v : V, v ^ 2 = 1) (h : MinParabolic X T M)
    (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    (hffJ : ffJ X = ⨆ H ∈ 𝓗, H) {L₀ L₁ : Subgroup (MulAut V)} (hL₀ : L₀ ∈ 𝓗) (hL₁ : L₁ ∈ 𝓗) :
    ∃ t ∈ T, B6.conjSub t L₀ = L₁ := by
  classical
  by_contra hcon
  have hJeq : Subgroup.closure (transvectionsIn X) = ⨆ H ∈ 𝓗, H := hb.iSup_eq.symm
  have hperm : ∀ g ∈ X, ∀ L ∈ 𝓗, B6.conjSub g L ∈ 𝓗 := fun g hg L hL =>
    conjSub_mem_of_blocks hV hb hffJ hg hL
  set 𝓞 := 𝓗.filter (fun L => ∃ t ∈ T, B6.conjSub t L₀ = L) with h𝓞
  set Y : Subgroup (MulAut V) := ⨆ L ∈ 𝓞, L with hY
  have h𝓞I : 𝓞 ⊆ 𝓗 := Finset.filter_subset _ _
  have hL₀𝓞 : L₀ ∈ 𝓞 := Finset.mem_filter.2 ⟨hL₀, 1, T.one_mem, B6.conjSub_one L₀⟩
  have hL₁𝓞 : L₁ ∉ 𝓞 := fun hm => hcon (Finset.mem_filter.1 hm).2
  have hYJ : Y ≤ ffJ X := hffJ ▸ iSup₂_le fun L hL =>
    le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) L (h𝓞I hL) le_rfl
  have hYX : Y ≤ X := hYJ.trans (B6.ffJ_le X)
  have hTY : ∀ t ∈ T, B6.conjSub t Y ≤ Y := by
    intro t ht
    simp only [hY, OrderIso.map_iSup]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨hLI, t', ht', hL'⟩ := Finset.mem_filter.1 hL
    have hmem : B6.conjSub t L ∈ 𝓞 := by
      refine Finset.mem_filter.2 ⟨hperm t (h.isSylow.1 ht) L hLI, t * t', T.mul_mem ht ht', ?_⟩
      rw [B6.conjSub_mul, hL']
    exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓞) => K) (B6.conjSub t L)
      hmem le_rfl
  have hKJ : twoResidual X ≤ ffJ X := h.twoResidual_le_ffJ hO hFF
  have hKY : ∀ k ∈ twoResidual X, B6.conjSub k Y ≤ Y := by
    intro k hk
    simp only [hY, OrderIso.map_iSup]
    refine iSup₂_le fun L hL => ?_
    have hkN := le_normalizer_of_blocks hb (h𝓞I hL) (hJeq ▸ hffJ ▸ hKJ hk)
    rw [B6.conjSub_eq_self hkN]
    exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓞) => K) L hL le_rfl
  have hYn : X ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
    rw [← sup_twoResidual_eq h.isSylow]
    refine sup_le (fun t ht => ?_) (fun k hk => ?_)
    · exact B6.mem_normalizer_of_conjSub_le (hTY t ht) (hTY t⁻¹ (T.inv_mem ht))
    · exact B6.mem_normalizer_of_conjSub_le (hKY k hk) (hKY k⁻¹ (Subgroup.inv_mem _ hk))
  rcases h.le_kerIn_or_twoResidual_le hYX hYn with hJ₀ | hK₀
  ·
    have hJodd : ¬ 2 ∣ Nat.card ↥(kerIn M X) := by
      have h1 := h.isSylowTwoOf_pCoreOf_kerIn.2.2
      rw [hO, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h1
      exact h1
    have hL₀J : L₀ ≤ kerIn M X :=
      (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓞) => K) L₀ hL₀𝓞 le_rfl).trans
        hJ₀
    have hdvd := Subgroup.card_dvd_of_le hL₀J
    rw [hb.card_eq L₀ hL₀] at hdvd
    exact hJodd ((by norm_num : 2 ∣ 6).trans hdvd)
  ·
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨f, hf3⟩ := exists_prime_orderOf_dvd_card' (G := ↥L₁) 3 (by
      rw [hb.card_eq L₁ hL₁]; norm_num)
    have hf3' : orderOf (f : MulAut V) = 3 := by rw [Subgroup.orderOf_coe]; exact hf3
    have hfK : (f : MulAut V) ∈ twoResidual X := by
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X (f : MulAut V)
        (hb.le_J hL₁ |>.trans (B1.closure_transvectionsIn_le X) f.2)
      exact B6.mem_of_pow_mem_of_coprime hk
        (by rw [hf3']; exact Nat.Coprime.pow_right _ (by norm_num))
    have hfY : (f : MulAut V) ∈ Y := hK₀ hfK
    have hYle : Y ≤ ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L₁), L' := by
      refine iSup₂_le fun L hL => ?_
      have hLne : L ≠ L₁ := fun he => hL₁𝓞 (he ▸ hL)
      exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) =>
        ⨆ (_ : K ≠ L₁), K) L (h𝓞I hL) (le_iSup (fun _ : L ≠ L₁ => L) hLne)
    have hf1 : (f : MulAut V) ∈ L₁ ⊓ ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L₁), L' := ⟨f.2, hYle hfY⟩
    rw [hb.inf_biSup_ne_eq_bot hL₁, Subgroup.mem_bot] at hf1
    rw [hf1, orderOf_one] at hf3'
    exact absurd hf3' (by norm_num)

theorem exists_two_involutions (hV : ∀ v : V, v ^ 2 = 1) {J : Subgroup (MulAut V)}
    (hb : IsTransvectionBlocks J 𝓗)
    {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by
  obtain ⟨a, ha⟩ := hb.exists_transvection hH
  have hsq : ∀ t ∈ transvectionsIn H, t ^ 2 = 1 := by
    intro t ht
    obtain ⟨-, ht1, w, htw⟩ := ht
    rw [pow_two]
    exact B1.tv_sq hV htw ht1
  by_contra hcon
  push Not at hcon
  have hall : ∀ t ∈ transvectionsIn H, t = a := by
    intro t ht
    by_contra hta
    exact ha.2.1 (hcon t ht.1 a ha.1 hta (hsq t ht) (hsq a ha) ht.2.1)
  have hle : H ≤ Subgroup.zpowers a := by
    rw [← hb.closure_eq H hH, Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, hall t ht]
    exact Subgroup.mem_zpowers a
  have h1 := Subgroup.card_le_of_le hle
  rw [hb.card_eq H hH, Nat.card_zpowers] at h1
  have h2 : orderOf a ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hsq a ha))
  omega


omit [CommGroup V] [Finite V] in
theorem inf_normalizer_eq_of_card {G : Type*} [Group G] [Finite G] {H P : Subgroup G}
    (hH6 : Nat.card H = 6) (hPH : P ≤ H) (hP2 : Nat.card P = 2)
    (hinv : ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1) :
    H ⊓ Subgroup.normalizer (P : Set G) = P := by
  have hPN : P ≤ H ⊓ Subgroup.normalizer (P : Set G) := le_inf hPH Subgroup.le_normalizer
  have hdvd : Nat.card ↥(H ⊓ Subgroup.normalizer (P : Set G)) ∣ 6 := by
    rw [← hH6]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd2 : 2 ∣ Nat.card ↥(H ⊓ Subgroup.normalizer (P : Set G)) := by
    rw [← hP2]
    exact Subgroup.card_dvd_of_le hPN
  by_cases h6 : Nat.card ↥(H ⊓ Subgroup.normalizer (P : Set G)) = 6
  · exfalso
    have hHN : H ⊓ Subgroup.normalizer (P : Set G) = H :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h6, hH6])
    have hHn : ∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set G) := fun h hh => by
      have hmem : h ∈ H ⊓ Subgroup.normalizer (P : Set G) := by rw [hHN]; exact hh
      exact hmem.2
    obtain ⟨τ, hτ1⟩ : ∃ τ : P, τ ≠ 1 := by
      have : Nontrivial P := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        omega
      exact exists_ne 1
    have hτsq : (τ : G) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := τ)
      rw [hP2] at this
      exact congrArg Subtype.val this
    have hτne : (τ : G) ≠ 1 := fun h => hτ1 (Subtype.ext h)
    have hunique := (Nat.card_eq_two_iff' (1 : P)).1 hP2
    obtain ⟨u, hu1, huu⟩ := hunique
    have hcent : ∀ h ∈ H, h * (τ : G) * h⁻¹ = (τ : G) := by
      intro h hh
      have hmem : h * (τ : G) * h⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hHn h hh) _).mp τ.2
      have hne1 : h * (τ : G) * h⁻¹ ≠ 1 := by
        intro h1
        apply hτne
        have : (τ : G) = h⁻¹ * (h * (τ : G) * h⁻¹) * h := by group
        rw [this, h1]
        group
      have e1 := huu ⟨_, hmem⟩ (fun h' => hne1 (congrArg Subtype.val h'))
      have e2 := huu τ hτ1
      exact congrArg Subtype.val (e1.trans e2.symm)
    obtain ⟨a, ha, b, hb, hab, ha2, hb2, ha1, hb1⟩ := hinv
    have hτH : (τ : G) ∈ H := hPH τ.2
    by_cases hτa : (τ : G) = a
    · have hc : (τ : G) * b = b * (τ : G) := by
        have := hcent b hb
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      exact IsTransvectionBlocks.not_commuting_involutions hH6 hτH hb hτsq hb2 hτne hb1
        (fun h => hab (hτa ▸ h)) hc
    · have hc : (τ : G) * a = a * (τ : G) := by
        have := hcent a ha
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      exact IsTransvectionBlocks.not_commuting_involutions hH6 hτH ha hτsq ha2 hτne ha1 hτa hc
  · have h2 : Nat.card ↥(H ⊓ Subgroup.normalizer (P : Set G)) = 2 := by
      have hle : Nat.card ↥(H ⊓ Subgroup.normalizer (P : Set G)) ≤ 6 :=
        Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card ↥(H ⊓ Subgroup.normalizer (P : Set G)) :=
        Nat.pos_of_dvd_of_pos hdvd (by norm_num)
      have h4 : Nat.card ↥(H ⊓ Subgroup.normalizer (P : Set G)) ≠ 4 := by
        intro h
        rw [h] at hdvd
        norm_num at hdvd
      obtain ⟨k, hk⟩ := hdvd2
      omega
    exact (Subgroup.eq_of_le_of_card_ge hPN (by rw [h2, hP2])).symm


theorem inf_ne_bot_of_blocks (hV : ∀ v : V, v ^ 2 = 1) (h : MinParabolic X T M)
    (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    (hffJ : ffJ X = ⨆ H ∈ 𝓗, H) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) : T ⊓ H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs2⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 (by
    rw [hb.card_eq H hH]; norm_num)
  have hs2' : orderOf (s : MulAut V) = 2 := by rw [Subgroup.orderOf_coe]; exact hs2
  have hsX : (s : MulAut V) ∈ X :=
    (hb.le_J hH |>.trans (B1.closure_transvectionsIn_le X)) s.2
  have hSp : IsPGroup 2 ↥(Subgroup.zpowers (s : MulAut V)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2']; norm_num)
  obtain ⟨S', hS', hSS'⟩ := exists_isSylowTwoOf_ge hSp (Subgroup.zpowers_le.2 hsX)
  obtain ⟨g, hgX, hgS⟩ := isSylowTwoOf_exists_conj h.isSylow hS'
  have hsS : (s : MulAut V) ∈ B6.conjSub g T :=
    hgS ▸ hSS' (Subgroup.mem_zpowers (s : MulAut V))
  rw [B6.mem_conjSub] at hsS
  set s' := g⁻¹ * (s : MulAut V) * g with hs'
  have hs'1 : s' ≠ 1 := by
    intro h1
    have : (s : MulAut V) = 1 := by
      have : (s : MulAut V) = g * s' * g⁻¹ := by rw [hs']; group
      rw [this, h1]
      group
    rw [this, orderOf_one] at hs2'
    exact absurd hs2' (by norm_num)
  have hH' : B6.conjSub g⁻¹ H ∈ 𝓗 := conjSub_mem_of_blocks hV hb hffJ (X.inv_mem hgX) hH
  have hs'H' : s' ∈ B6.conjSub g⁻¹ H := by
    rw [B6.mem_conjSub]
    simp [hs', mul_assoc]
  obtain ⟨t, htT, hH'H⟩ := exists_conjSub_of_blocks hV h hO hFF hb hffJ hH' hH
  have hxH : t * s' * t⁻¹ ∈ H := by
    rw [← hH'H]
    exact B6.mem_conjSub.2 (by simpa [mul_assoc] using hs'H')
  have hx : t * s' * t⁻¹ ∈ T ⊓ H :=
    ⟨T.mul_mem (T.mul_mem htT hsS) (T.inv_mem htT), hxH⟩
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hx
  apply hs'1
  have : s' = t⁻¹ * (t * s' * t⁻¹) * t := by group
  rw [this, hx]
  group

theorem card_inf_eq_two (hV : ∀ v : V, v ^ 2 = 1) (h : MinParabolic X T M)
    (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    (hffJ : ffJ X = ⨆ H ∈ 𝓗, H) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    Nat.card ↥(T ⊓ H) = 2 := by
  have hne := inf_ne_bot_of_blocks hV h hO hFF hb hffJ hH
  have hP : IsPGroup 2 ↥(T ⊓ H) := h.isSylow.2.1.to_le inf_le_left
  have hcard : Nat.card ↥(T ⊓ H) = 2 ^ rk ↥(T ⊓ H) := card_eq_two_pow_of_isPGroup hP
  have hdvd : Nat.card ↥(T ⊓ H) ∣ 6 := by
    rw [← hb.card_eq H hH]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h1 : Nat.card ↥(T ⊓ H) ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.1 h1)
  have hle : Nat.card ↥(T ⊓ H) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  rw [hcard] at h1 hdvd hle ⊢
  generalize rk ↥(T ⊓ H) = m at h1 hdvd hle ⊢
  rcases m with _ | _ | _ | m
  · simp at h1
  · simp
  · norm_num at hdvd
  · exfalso
    have : 2 ^ (m + 3) ≥ 8 := by
      calc 2 ^ (m + 3) = 2 ^ m * 8 := by ring
        _ ≥ 1 * 8 := Nat.mul_le_mul_right 8 (Nat.one_le_two_pow)
    omega

theorem inf_M_eq (hV : ∀ v : V, v ^ 2 = 1) (h : MinParabolic X T M)
    (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    (hffJ : ffJ X = ⨆ H ∈ 𝓗, H) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) : M ⊓ H = T ⊓ H := by
  have hP2 := card_inf_eq_two hV h hO hFF hb hffJ hH
  have hPQ : T ⊓ H ≤ M ⊓ H := inf_le_inf_right H h.le
  have hdvd : Nat.card ↥(M ⊓ H) ∣ 6 := by
    rw [← hb.card_eq H hH]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hdvd2 : 2 ∣ Nat.card ↥(M ⊓ H) := by
    rw [← hP2]
    exact Subgroup.card_dvd_of_le hPQ
  by_cases h6 : Nat.card ↥(M ⊓ H) = 6
  · exfalso
    have hHM : H ≤ M := by
      have : M ⊓ H = H :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h6, hb.card_eq H hH])
      rw [← this]
      exact inf_le_left
    have hall : ∀ H' ∈ 𝓗, H' ≤ M := by
      intro H' hH'
      obtain ⟨t, htT, rfl⟩ := exists_conjSub_of_blocks hV h hO hFF hb hffJ hH hH'
      calc B6.conjSub t H ≤ B6.conjSub t M := (B6.conjSub t).monotone hHM
        _ = M := B6.conjSub_eq_self (Subgroup.le_normalizer (h.le htT))
    have hfJM : ffJ X ≤ M := hffJ ▸ iSup₂_le fun H' hH' => hall H' hH'
    have hKM : twoResidual X ≤ M := (h.twoResidual_le_ffJ hO hFF).trans hfJM
    exact h.not_twoResidual_le_kerIn
      (le_kerIn_of_le_normalizer hKM (le_normalizer_twoResidual X))
  · have h2 : Nat.card ↥(M ⊓ H) = 2 := by
      have hle : Nat.card ↥(M ⊓ H) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card ↥(M ⊓ H) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
      have h4 : Nat.card ↥(M ⊓ H) ≠ 4 := by
        intro h4
        rw [h4] at hdvd
        norm_num at hdvd
      obtain ⟨k, hk⟩ := hdvd2
      omega
    exact (Subgroup.eq_of_le_of_card_ge hPQ (by rw [h2, hP2])).symm

theorem structConcl_of_solvable (hV : ∀ v : V, v ^ 2 = 1) (h : MinParabolic X T M)
    (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) (hsolv : Group.IsSolvable ↥X) :
    ∃ 𝓗 : Finset (Subgroup (MulAut V)), StructConcl X T M 𝓗 := by
  have hO' := normal_two_subgroups_trivial_of_pCoreOf_eq_bot hO
  have hJX := B1.closure_transvectionsIn_le X
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn X)) :=
    B1.solvable_of_le hJX hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO'
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn X))) =
      Subgroup.closure (transvectionsIn X) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hV hsolvJ hOJ hcl
  have hffJ : ffJ X = ⨆ H ∈ 𝓗, H := hb.ffJ_eq hV hsolv hO'
  have hJ' : ffJ X = Subgroup.closure (transvectionsIn X) := hffJ.trans hb.iSup_eq
  refine ⟨𝓗, fun H hH => (hb.le_J hH).trans hJX, hffJ, hb.comm,
    fun H hH => hb.inf_biSup_ne_eq_bot hH, ?_, fun H hH => ?_, ?_,
    fun H hH H' hH' => exists_conjSub_of_blocks hV h hO hFF hb hffJ hH hH',
    h.eq_sup_ffJ hO hFF, fun H hH => ?_⟩
  · rw [hJ', commV_iSup_eq hb]
  · rw [hJ']
    exact commSub_sup_fixV_inf hV hb hH
  · intro H hH H' hH' hne
    rw [commSub_eq_bot_iff]
    intro u hu g hg
    rw [commV_eq_commSub] at hu
    exact hb.triv H' hH' H hH (Ne.symm hne) g hg u hu
  · refine Or.inl ⟨1, le_rfl, ?_, ?_⟩
    · have hHJ : H ≤ ffJ X := hffJ ▸ le_iSup₂ (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) H hH
      have hZ : commV H ⊓ fixV (ffJ X) = ⊥ := by
        refine le_bot_iff.1 ?_
        calc commV H ⊓ fixV (ffJ X) ≤ commV H ⊓ fixV H := inf_le_inf_left _ (fixV_anti hHJ)
          _ = ⊥ := by
            rw [inf_comm, commV_eq_commSub]
            exact IsTransvectionBlocks.fixV_inf_commSub hV hb hH
      have hnat := FFC.binaryNaturalSL_two_of_s3 hV (hb.card_eq H hH) (U := commV H) (C := ⊥)
        (by rw [commV_eq_commSub]; exact hb.card_comm H hH)
        (by rw [commV_eq_commSub]; exact hb.stab H hH)
        (fun g hg hgu => by
          have hmem : g ∈ H ⊓ centSub (commSub (⊤ : Subgroup V) H) :=
            ⟨hg, fun u hu => hgu u (by rwa [commV_eq_commSub])⟩
          rw [hb.inf_centSub hH, Subgroup.mem_bot] at hmem
          exact hmem)
        (fun g _ c hc => by
          rw [Subgroup.mem_bot] at hc
          rw [hc, map_one]
          exact Subgroup.one_mem _)
        (inf_bot_eq _)
      rw [sup_bot_eq] at hnat
      rw [hZ]
      exact hnat
    · rw [inf_M_eq hV h hO hFF hb hffJ hH, inf_normalizer_eq_of_card (hb.card_eq H hH) inf_le_right
        (card_inf_eq_two hV h hO hFF hb hffJ hH) (exists_two_involutions hV hb hH)]

end Solv

end B69

end CFSG.Quasithin
