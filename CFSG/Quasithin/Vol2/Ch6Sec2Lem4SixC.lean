module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4Six
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4SixB
public import CFSG.Quasithin.Vol2.Ch11SecD556A
public import CFSG.Quasithin.H13.U3S1348H
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem res624Six_of (h36 : A36ForSQTK) (h37 : A37ForSQTK) : Res624Six := by
  intro G _ _ T M L V h U hUV hm hH hTU hchar hLU hLUH K K' hK₀ hK'₀ h3K h3K'
  classical
  have hK : K ∈ cComp (Subgroup.centralizer (U : Set G)) := hK₀
  have hK' : K' ∈ cComp (Subgroup.centralizer (U : Set G)) := hK'₀
  by_contra hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set N := Subgroup.normalizer (U : Set G) with hNdef
  set O := pCoreOf 2 H with hOdef
  set LU := oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G)) with hLUdef
  have hU4 : Nat.card U = 4 := h.card_of_mQuot_two hUV hm
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hU4
    omega
  have hVab := h.toHyp611.isElemAbelian
  have hU2 : IsPGroup 2 U := (B2F.isPGroup_of_isElemAbelian hVab).to_le hUV
  have hHN : H ≤ N := Subgroup.centralizer_le_normalizer _
  have hUH : U ≤ H := fun u hu => Subgroup.mem_centralizer_iff.mpr fun u' hu' =>
    B2F.isElemAbelian_comm hVab (hUV hu') (hUV hu)
  have hUO : U ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUH hHN hU2
  have hO1 : O ≠ ⊥ := fun h0 => hU1 (eq_bot_iff.mpr (h0 ▸ hUO))
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hOH : O ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hON : N ≤ Subgroup.normalizer (O : Set G) := fun n hn =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (mem_normalizer_centralizer_ch62 hn)
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK'H : K' ≤ H := le_of_mem_cComp hK'
  have h3LU : 3 ∣ Nat.card LU := ⟨_, hLU⟩
  obtain ⟨d₀, hd₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥LU) 3 h3LU
  set d : G := (d₀ : G) with hd
  have hd3 : orderOf d = 3 := by rw [hd, Subgroup.orderOf_coe, hd₀]
  have hdN : d ∈ N := ((oTwoUpper_le _).trans inf_le_right) d₀.2
  have hdH : d ∉ H := by
    intro hdH
    have hmem : d ∈ pCoreOf 2 LU := by rw [hLUH]; exact ⟨d₀.2, hdH⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LU) ⟨d, hmem⟩
    have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hd3] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
    omega
  have hdNH : d ∈ Subgroup.normalizer (H : Set G) := mem_normalizer_centralizer_ch62 hdN
  have hnab : ∃ a b : G, a * b ≠ b * a := h.nonabelian
  have hcommC : ∀ J J' : Subgroup G, J ∈ cComp H → J' ∈ cComp H → J ≠ J' → ⁅J, J'⁆ ≤ O :=
    fun J J' hJ hJ' hne' => commutator_le_pCoreOf_of_ne
      (h37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot h.qtke h.simple hnab hO1)) hJ hJ' hne'
  have hα : ∀ J ∈ cComp H, 3 ∣ Nat.card J →
      ∃ x ∈ J, orderOf x = 3 ∧ ∃ k ∈ J, x * k * x⁻¹ * k⁻¹ ∉ O := fun J hJ h3 =>
    exists_noncentral_three_of_cComp624 h36 h.qtke h.simple hnab hO1 hJ h3
  have hOsub : (O.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hOH.trans hHN)]
    exact hON
  set π := QuotientGroup.mk' (O.subgroupOf N) with hπ
  have hπ1 : ∀ (g : G) (hg : g ∈ N), π ⟨g, hg⟩ = 1 ↔ g ∈ O := by
    intro g hg
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπcomm : ∀ (g g' : G) (hg : g ∈ N) (hg' : g' ∈ N),
      Commute (π ⟨g, hg⟩) (π ⟨g', hg'⟩) ↔ g * g' * g⁻¹ * g'⁻¹ ∈ O := by
    intro g g' hg hg'
    have hc : g * g' * g⁻¹ * g'⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem hg hg') (N.inv_mem hg)) (N.inv_mem hg')
    rw [← hπ1 _ hc]
    have e : π ⟨g * g' * g⁻¹ * g'⁻¹, hc⟩ =
        π ⟨g, hg⟩ * π ⟨g', hg'⟩ * (π ⟨g, hg⟩)⁻¹ * (π ⟨g', hg'⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e, Commute, SemiconjBy]
    constructor
    · intro h1
      rw [h1]
      group
    · intro h1
      calc π ⟨g, hg⟩ * π ⟨g', hg'⟩ = (π ⟨g, hg⟩ * π ⟨g', hg'⟩ * (π ⟨g, hg⟩)⁻¹ *
          (π ⟨g', hg'⟩)⁻¹) * (π ⟨g', hg'⟩ * π ⟨g, hg⟩) := by group
        _ = π ⟨g', hg'⟩ * π ⟨g, hg⟩ := by rw [h1, one_mul]
  have hπo : ∀ (g : G) (hg : g ∈ N), orderOf g = 3 → orderOf (π ⟨g, hg⟩) = 3 := by
    intro g hg hg3
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨g, hg⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by rw [← hg3]; simp [pow_orderOf_eq_one])
      rw [this, map_one]
    · intro h1
      have hgO := (hπ1 g hg).mp h1
      obtain ⟨k, hk⟩ := hO2 ⟨g, hgO⟩
      have h2 : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hg3] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      omega
  have hev : CFSG.Assembly.evenRank G ≤ 2 := h.qtke.2.2
  have hrankN : ∀ E : Subgroup G, E ≤ N → IsElemAbelian 3 E → ∀ r, Nat.card E = 3 ^ r →
      r ≤ 2 := fun E hEN hE r hr =>
    Vol2.Ch11.SecD.le_two_of_elemAbelian hev hU1 hU2 Nat.prime_three (by norm_num) hEN hE hr
  have hker : ∀ x : ↥N, π x = 1 → ∃ i : ℕ, x ^ 2 ^ i = 1 := by
    intro x hx
    have hxO := (hπ1 x x.2).mp hx
    obtain ⟨i, hi⟩ := hO2 ⟨x, hxO⟩
    exact ⟨i, Subtype.ext (by simpa using congrArg Subtype.val hi)⟩
  have hrankY : ∀ E : Subgroup (↥N ⧸ O.subgroupOf N), IsElemAbelian 3 E →
      Nat.card E = 3 ^ 3 → False := fun E hE hE27 => by
    have := U3.le_two_of_elemAbelian_of_surjective π (QuotientGroup.mk'_surjective _) hker
      Nat.prime_three (by norm_num) hrankN hE hE27
    omega
  have hJN : ∀ {J : Subgroup G}, J ∈ cComp H → J ≤ N := fun hJ => (le_of_mem_cComp hJ).trans hHN
  have hcentral : ∀ (J : Subgroup G) (hJN' : J ≤ N) (x : G) (hx : x ∈ J), orderOf x = 3 →
      (∃ k ∈ J, x * k * x⁻¹ * k⁻¹ ∉ O) →
      ∀ c ∈ Subgroup.zpowers (π ⟨x, hJN' hx⟩),
        (∀ (k : G) (hk : k ∈ J), Commute c (π ⟨k, hJN' hk⟩)) → c = 1 := by
    intro J hJN' x hx hx3 hnc c hc hcc
    obtain ⟨k, hk, hxk⟩ := hnc
    by_contra hc1
    obtain ⟨i, hi⟩ := mem_zpowers_of_ne_one624 (hπo x _ hx3) hc hc1
    apply hxk
    rw [← hπcomm x k (hJN' hx) (hJN' hk)]
    have := (hcc k hk).zpow_left i
    simp only at hi
    rwa [hi] at this
  have hcommπ : ∀ (J J' : Subgroup G) (hJ : J ∈ cComp H) (hJ' : J' ∈ cComp H), J ≠ J' →
      ∀ (x : G) (hx : x ∈ J) (y : G) (hy : y ∈ J'),
        Commute (π ⟨x, hJN hJ hx⟩) (π ⟨y, hJN hJ' hy⟩) := by
    intro J J' hJ hJ' hne' x hx y hy
    rw [hπcomm]
    have := hcommC J J' hJ hJ' hne' (Subgroup.commutator_mem_commutator hx hy)
    rwa [commutatorElement_def] at this
  have hncd : ∀ (J : Subgroup G) (x : G), (∃ k ∈ J, x * k * x⁻¹ * k⁻¹ ∉ O) →
      ∃ k ∈ J.map (MulAut.conj d).toMonoidHom,
        (d * x * d⁻¹) * k * (d * x * d⁻¹)⁻¹ * k⁻¹ ∉ O := by
    rintro J x ⟨k, hk, hxk⟩
    refine ⟨d * k * d⁻¹, ⟨k, hk, by simp [MulAut.conj_apply]⟩, fun hmem => hxk ?_⟩
    have e : x * k * x⁻¹ * k⁻¹ =
        d⁻¹ * ((d * x * d⁻¹) * (d * k * d⁻¹) * (d * x * d⁻¹)⁻¹ * (d * k * d⁻¹)⁻¹) * d⁻¹⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hON (N.inv_mem hdN)) _).mp hmem
  have hHd : H.map (MulAut.conj d).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hdNH
  have hmove : ∀ J ∈ cComp H, 3 ∣ Nat.card J → d ∈ Subgroup.normalizer (J : Set G) := by
    intro J hJ h3J
    by_contra hdJ
    set c := MulAut.conj d with hc
    set J₂ := J.map c.toMonoidHom with hJ₂def
    set J₃ := J₂.map c.toMonoidHom with hJ₃def
    have hJ₂ : J₂ ∈ cComp H := by
      have := cComp_map_mulEquiv c hJ
      rwa [hHd] at this
    have hJ₃ : J₃ ∈ cComp H := by
      have := cComp_map_mulEquiv c hJ₂
      rwa [hHd] at this
    have h12 : J ≠ J₂ := fun h12 => hdJ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h12.symm)
    have h23 : J₂ ≠ J₃ := fun h23 => h12 (Subgroup.map_injective c.injective h23)
    have h13 : J ≠ J₃ := by
      intro h13
      have hJ₃e : J₃ = J.map (MulAut.conj (d * d)).toMonoidHom := by
        rw [hJ₃def, hJ₂def, Subgroup.map_map, map_mul]
        rfl
      have hdd : d * d ∈ Subgroup.normalizer (J : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hJ₃e ▸ h13).symm
      apply hdJ
      have e : d = (d * d) * (d * d) := by
        have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
        calc d = d ^ 3 * d := by rw [hd3', one_mul]
          _ = (d * d) * (d * d) := by rw [pow_succ, pow_succ, pow_one]; group
      rw [e]
      exact Subgroup.mul_mem _ hdd hdd
    obtain ⟨x, hx, hx3, hnc⟩ := hα J hJ h3J
    set x₂ := d * x * d⁻¹ with hx₂def
    set x₃ := d * x₂ * d⁻¹ with hx₃def
    have hx₂ : x₂ ∈ J₂ := ⟨x, hx, by simp [hc, MulAut.conj_apply, hx₂def]⟩
    have hx₃ : x₃ ∈ J₃ := ⟨x₂, hx₂, by simp [hc, MulAut.conj_apply, hx₃def]⟩
    have hx₂o : orderOf x₂ = 3 := by
      rw [hx₂def, show d * x * d⁻¹ = (MulAut.conj d) x by simp, MulEquiv.orderOf_eq, hx3]
    have hx₃o : orderOf x₃ = 3 := by
      rw [hx₃def, show d * x₂ * d⁻¹ = (MulAut.conj d) x₂ by simp, MulEquiv.orderOf_eq, hx₂o]
    have hnc₂ := hncd J x hnc
    have hnc₃ := hncd J₂ x₂ hnc₂
    obtain ⟨E, hE, hE27⟩ := exists_elemAbelian27_of_elements624 (hπo x (hJN hJ hx) hx3)
      (hπo x₂ (hJN hJ₂ hx₂) hx₂o) (hπo x₃ (hJN hJ₃ hx₃) hx₃o)
      (hcommπ J J₂ hJ hJ₂ h12 x hx x₂ hx₂) (hcommπ J J₃ hJ hJ₃ h13 x hx x₃ hx₃)
      (hcommπ J₂ J₃ hJ₂ hJ₃ h23 x₂ hx₂ x₃ hx₃) (by
        intro a ha b hb e he habe
        obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        dsimp only at habe ⊢
        have hak : ∀ (k : G) (hk : k ∈ J₃), Commute ((π ⟨x, hJN hJ hx⟩) ^ i)
            (π ⟨k, hJN hJ₃ hk⟩) := fun k hk =>
          (hcommπ J J₃ hJ hJ₃ h13 x hx k hk).zpow_left i
        have hbk : ∀ (k : G) (hk : k ∈ J₃), Commute ((π ⟨x₂, hJN hJ₂ hx₂⟩) ^ j)
            (π ⟨k, hJN hJ₃ hk⟩) := fun k hk =>
          (hcommπ J₂ J₃ hJ₂ hJ₃ h23 x₂ hx₂ k hk).zpow_left j
        have he' : e = ((π ⟨x, hJN hJ hx⟩) ^ i * (π ⟨x₂, hJN hJ₂ hx₂⟩) ^ j)⁻¹ :=
          eq_inv_of_mul_eq_one_right habe
        have he1 : e = 1 := hcentral J₃ (hJN hJ₃) x₃ hx₃ hx₃o hnc₃ e he fun k hk => by
          rw [he']
          exact ((hak k hk).mul_left (hbk k hk)).inv_left
        rw [he1, mul_one] at habe
        have hb' : (π ⟨x₂, hJN hJ₂ hx₂⟩) ^ j = ((π ⟨x, hJN hJ hx⟩) ^ i)⁻¹ :=
          eq_inv_of_mul_eq_one_right habe
        have hb1 : (π ⟨x₂, hJN hJ₂ hx₂⟩) ^ j = 1 :=
          hcentral J₂ (hJN hJ₂) x₂ hx₂ hx₂o hnc₂ _ ⟨j, rfl⟩ fun k hk => by
            rw [hb']
            exact ((hcommπ J J₂ hJ hJ₂ h12 x hx k hk).zpow_left i).inv_left
        rw [hb1, mul_one] at habe
        exact ⟨habe, hb1, he1⟩)
    exact hrankY E hE hE27
  have hdK := hmove K hK h3K
  have hdK' := hmove K' hK' h3K'
  have hE9 : ∀ (J J' : Subgroup G) (hJ : J ∈ cComp H) (hJ' : J' ∈ cComp H), J ≠ J' →
      3 ∣ Nat.card J' → ∀ (e₁ : G) (h₁ : e₁ ∈ J) (e₂ : G) (h₂ : e₂ ∈ J), orderOf e₁ = 3 →
      orderOf e₂ = 3 → Commute (π ⟨e₁, hJN hJ h₁⟩) (π ⟨e₂, hJN hJ h₂⟩) →
      π ⟨e₂, hJN hJ h₂⟩ ∉ Subgroup.zpowers (π ⟨e₁, hJN hJ h₁⟩) → False := by
    intro J J' hJ hJ' hne' h3J' e₁ h₁ e₂ h₂ ho₁ ho₂ hc₁₂ hnot
    obtain ⟨y, hy, hy3, hncy⟩ := hα J' hJ' h3J'
    obtain ⟨E, hE, hE27⟩ := exists_elemAbelian27_of_elements624 (hπo e₁ _ ho₁)
      (hπo e₂ _ ho₂) (hπo y (hJN hJ' hy) hy3) hc₁₂ (hcommπ J J' hJ hJ' hne' e₁ h₁ y hy)
      (hcommπ J J' hJ hJ' hne' e₂ h₂ y hy) (by
        intro a ha b hb e he habe
        obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        dsimp only at habe ⊢
        have he' : e = ((π ⟨e₁, hJN hJ h₁⟩) ^ i * (π ⟨e₂, hJN hJ h₂⟩) ^ j)⁻¹ :=
          eq_inv_of_mul_eq_one_right habe
        have he1 : e = 1 := hcentral J' (hJN hJ') y hy hy3 hncy e he fun k hk => by
          rw [he']
          exact (((hcommπ J J' hJ hJ' hne' e₁ h₁ k hk).zpow_left i).mul_left
            ((hcommπ J J' hJ hJ' hne' e₂ h₂ k hk).zpow_left j)).inv_left
        rw [he1, mul_one] at habe
        have hb' : (π ⟨e₂, hJN hJ h₂⟩) ^ j = ((π ⟨e₁, hJN hJ h₁⟩) ^ i)⁻¹ :=
          eq_inv_of_mul_eq_one_right habe
        have hb1 : (π ⟨e₂, hJN hJ h₂⟩) ^ j = 1 := by
          by_contra hb1
          apply hnot
          have h1 := mem_zpowers_of_ne_one624 (hπo e₂ _ ho₂) ⟨j, rfl⟩ hb1
          have h2 : (π ⟨e₂, hJN hJ h₂⟩) ^ j ∈ Subgroup.zpowers (π ⟨e₁, hJN hJ h₁⟩) := by
            rw [hb']
            exact Subgroup.inv_mem _ ⟨i, rfl⟩
          exact Subgroup.zpowers_le.mpr h2 h1
        rw [hb1, mul_one] at habe
        exact ⟨habe, hb1, he1⟩)
    exact hrankY E hE hE27
  have hd3p : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd3, pow_one])
  obtain ⟨w, ⟨hwK, hwd⟩, hw3⟩ :=
    exists_orderOf_three_mem_centralizer624 (Subgroup.zpowers_le.mpr hdK) hd3p h3K
  obtain ⟨w', ⟨hw'K', hw'd⟩, hw'3⟩ :=
    exists_orderOf_three_mem_centralizer624 (Subgroup.zpowers_le.mpr hdK') hd3p h3K'
  have hncw : ∀ (J J' : Subgroup G) (hJ : J ∈ cComp H) (hJ' : J' ∈ cComp H), J ≠ J' →
      3 ∣ Nat.card J → 3 ∣ Nat.card J' → ∀ v ∈ J, orderOf v = 3 →
      ∃ k ∈ J, v * k * v⁻¹ * k⁻¹ ∉ O := by
    intro J J' hJ hJ' hne' h3J h3J' v hv hv3
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, hx3, hncx⟩ := hα J hJ h3J
    refine hE9 J J' hJ hJ' hne' h3J' v hv x hx hv3 hx3 ((hπcomm v x _ _).mpr (hcon x hx)) ?_
    rintro ⟨i, hi⟩
    obtain ⟨k, hk, hxk⟩ := hncx
    apply hxk
    rw [← hπcomm x k (hJN hJ hx) (hJN hJ hk)]
    have := ((hπcomm v k (hJN hJ hv) (hJN hJ hk)).mpr (hcon k hk)).zpow_left i
    simp only at hi
    rwa [hi] at this
  have hncw₁ := hncw K K' hK hK' hne h3K h3K' w hwK hw3
  have hncw₂ := hncw K' K hK' hK (Ne.symm hne) h3K' h3K w' hw'K' hw'3
  have hcd : ∀ (v : G) (hv : v ∈ N), v ∈ Subgroup.centralizer (Subgroup.zpowers d : Set G) →
      Commute (π ⟨v, hv⟩) (π ⟨d, hdN⟩) := by
    intro v hv hvd
    rw [hπcomm]
    have := Subgroup.mem_centralizer_iff.mp hvd d (Subgroup.mem_zpowers d)
    rw [← this, mul_inv_cancel_right, mul_inv_cancel]
    exact O.one_mem
  obtain ⟨E, hE, hE27⟩ := exists_elemAbelian27_of_elements624 (hπo w (hJN hK hwK) hw3)
    (hπo w' (hJN hK' hw'K') hw'3) (hπo d hdN hd3) (hcommπ K K' hK hK' hne w hwK w' hw'K')
    (hcd w _ hwd) (hcd w' _ hw'd) (by
      intro a ha b hb e he habe
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      dsimp only at habe ⊢
      have he' : e = ((π ⟨w, hJN hK hwK⟩) ^ i * (π ⟨w', hJN hK' hw'K'⟩) ^ j)⁻¹ :=
        eq_inv_of_mul_eq_one_right habe
      have he1 : e = 1 := by
        by_contra he1
        obtain ⟨k, hk⟩ := mem_zpowers_of_ne_one624 (hπo d hdN hd3) he he1
        have hwH : (w ^ i * w' ^ j)⁻¹ ^ k ∈ H := by
          refine H.zpow_mem (H.inv_mem (H.mul_mem (H.zpow_mem (hKH hwK) i)
            (H.zpow_mem (hK'H hw'K') j))) k
        have hval : π ⟨(w ^ i * w' ^ j)⁻¹ ^ k, hHN hwH⟩ = π ⟨d, hdN⟩ := by
          rw [← hk, he']
          rfl
        apply hdH
        have h1 : π ⟨d * ((w ^ i * w' ^ j)⁻¹ ^ k)⁻¹,
            N.mul_mem hdN (N.inv_mem (hHN hwH))⟩ = 1 := by
          rw [show (⟨d * ((w ^ i * w' ^ j)⁻¹ ^ k)⁻¹, N.mul_mem hdN (N.inv_mem (hHN hwH))⟩ : ↥N) =
            ⟨d, hdN⟩ * (⟨(w ^ i * w' ^ j)⁻¹ ^ k, hHN hwH⟩ : ↥N)⁻¹ from rfl, map_mul, map_inv,
            hval, mul_inv_cancel]
        have h2 := hOH ((hπ1 _ _).mp h1)
        have h3 := H.mul_mem h2 hwH
        simpa using h3
      rw [he1, mul_one] at habe
      have hb' : (π ⟨w', hJN hK' hw'K'⟩) ^ j = ((π ⟨w, hJN hK hwK⟩) ^ i)⁻¹ :=
        eq_inv_of_mul_eq_one_right habe
      have hb1 : (π ⟨w', hJN hK' hw'K'⟩) ^ j = 1 :=
        hcentral K' (hJN hK') w' hw'K' hw'3 hncw₂ _ ⟨j, rfl⟩ fun k hk => by
          rw [hb']
          exact ((hcommπ K K' hK hK' hne w hwK k hk).zpow_left i).inv_left
      rw [hb1, mul_one] at habe
      exact ⟨habe, hb1, he1⟩)
  exact hrankY E hE hE27

end CFSG.Quasithin.H13
