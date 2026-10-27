module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch10SecABasicL0
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

@[expose] def Fact3_3_25Theta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G), Setup331 G T M L →
    M ≤ Subgroup.normalizer (L : Set G) →
    (IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L) →
    ∀ x ∈ M, orderOf x = 3 → x ∈ L

@[expose] def Fact3_3_25XS3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) →
    (IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨ IsLnBlock L 3) →
    Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ⧸
      CFSG.pCore 2
        ↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ≃*
      Equiv.Perm (Fin 3))

@[expose] def Insp3_3_25Hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → CFSG.Quasithin.IsHatA6Block L →
    (∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2
        (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T)) A →
      A ≤ qL L T) ∧
    (tC L T = ⊥ → vPlus L T = qL L T) ∧
    (vPlus L T = qL L T →
      (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥(vPlus L T)) ∧
      (∀ B : Subgroup G, IsMaxElemAbelian T B → ¬ B ≤ vPlus L T →
        ∃ b ∈ B, vPlus L T ⊓ Subgroup.centralizer (B : Set G) =
          vPlus L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
      ∀ B B' : Subgroup G, IsMaxElemAbelian T B → IsMaxElemAbelian T B' →
        ¬ B ≤ vPlus L T → ¬ B' ≤ vPlus L T → B ⊔ vPlus L T = B' ⊔ vPlus L T)

@[expose] def Insp3_3_25Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → (IsG2Block L ∨ IsLnBlock L 3) → tC L T = ⊥ →
    vPlus L T ≠ qL L T →
    (∃ _ : IsMulCommutative ↥(vPlus L T), IsFFModule (V := ↥(vPlus L T))
      (autOn (L ⊔ T) (vPlus L T))) →
    ¬ IsG2Block L ∧
    (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥(qL L T)) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian T B → ¬ B ≤ qL L T →
      ∃ b ∈ B, qL L T ⊓ Subgroup.centralizer (B : Set G) =
        qL L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    ∀ B B' : Subgroup G, IsMaxElemAbelian T B → IsMaxElemAbelian T B' →
      ¬ B ≤ qL L T → ¬ B' ≤ qL L T → B ⊔ qL L T = B' ⊔ qL L T

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

namespace Lem3325

theorem unique_of_offenders {H Q : Subgroup G} (hQe : IsElemAbelian 2 Q) (hQH : Q ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (hC : H ⊓ Subgroup.centralizer (Q : Set G) = Q)
    (ha : ∀ B : Subgroup G, B ≤ H → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥Q)
    (hb : ∀ B : Subgroup G, IsMaxElemAbelian H B → ¬ B ≤ Q →
      ∃ b ∈ B, Q ⊓ Subgroup.centralizer (B : Set G) = Q ⊓ Subgroup.centralizer ({b} : Set G))
    (hc : ∀ B B' : Subgroup G, IsMaxElemAbelian H B → IsMaxElemAbelian H B' →
      ¬ B ≤ Q → ¬ B' ≤ Q → B ⊔ Q = B' ⊔ Q) :
    IsMaxElemAbelian H Q ∧ ∀ A A' : Subgroup G, IsMaxElemAbelian H A →
      IsMaxElemAbelian H A' → A ≠ Q → A' ≠ Q → A = A' := by
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hQmax : IsMaxElemAbelian H Q := ⟨hQH, hQe, ha⟩
  refine ⟨hQmax, fun A A' hA hA' hAQ hA'Q => ?_⟩
  have hout : ∀ B : Subgroup G, IsMaxElemAbelian H B → B ≠ Q → ¬ B ≤ Q :=
    fun B hB hne hle => hne (Subgroup.eq_of_le_of_card_ge hle (hB.2.2 _ hQH hQe))
  obtain ⟨b, hbA, hbC⟩ := hb A hA (hout A hA hAQ)
  have hsup := hc A A' hA hA' (hout A hA hAQ) (hout A' hA' hA'Q)
  have hauto : autI hQe A = autI hQe A' := by
    rw [autI_eq_autOn, autI_eq_autOn, ← autOn_sup_eq_of_comm hQab (hA.1.trans hHN), hsup,
      autOn_sup_eq_of_comm hQab (hA'.1.trans hHN)]
  exact (B2_21 hQe hQH hHN hC hA hbA hbC hA' hauto).symm

end Lem3325

open Lem3325 Lem3331

omit [Finite G] in
theorem conj_mem_omegaOneCenter {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) : g * z * g⁻¹ ∈ quasithinOmegaOneCenter T := by
  induction hz using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨hyT, hyC⟩, hy2⟩ := hy
    refine Subgroup.subset_closure ⟨⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyT, ?_⟩, ?_⟩
    · show g * y * g⁻¹ ∈ Subgroup.centralizer (T : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : g⁻¹ * t * g ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hyC _ ht'
      calc t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * t := by group
    · show (g * y * g⁻¹) ^ 2 = 1
      rw [conj_pow, hy2, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b _ _ iha ihb => simpa [mul_assoc] using (quasithinOmegaOneCenter T).mul_mem iha ihb
  | inv a _ ih => simpa [mul_assoc] using (quasithinOmegaOneCenter T).inv_mem ih

omit [Finite G] in
theorem conj_mem_centralizer_omegaOneCenter {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G))
    {x : G} (hx : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro z hz
  have hz' : g⁻¹ * z * g ∈ quasithinOmegaOneCenter T := by
    have := conj_mem_omegaOneCenter (Subgroup.inv_mem _ hg) hz
    simpa using this
  have h1 := hx _ hz'
  calc z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * z := by group

theorem mem_normalizer_thompsonJ {H : Subgroup G} {g : G}
    (hg : ∀ A : Subgroup G, IsMaxElemAbelian H A →
      IsMaxElemAbelian H (A.map (MulAut.conj g).toMonoidHom)) :
    g ∈ Subgroup.normalizer (thompsonJ H : Set G) := by
  have hle : (thompsonJ H).map (MulAut.conj g).toMonoidHom ≤ thompsonJ H := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact GammaExtra.le_thompsonJ (hg A hA)
  refine A38.map_conj_eq_iff.mp (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem thompsonJ_ne_bot' {H : Subgroup G} (hH : IsPGroup 2 ↥H) (hne : H ≠ ⊥) :
    thompsonJ H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian H
  have hnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  obtain ⟨⟨x, hxH⟩, hx2⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2
    (by
      obtain ⟨n, hn⟩ := hH.exists_card_eq
      have h1 : 1 < Nat.card ↥H := Finite.one_lt_card_iff_nontrivial.mpr hnt
      rw [hn] at h1 ⊢
      exact dvd_pow_self 2 (by rintro rfl; simp at h1))
  have hxo : orderOf x = 2 := by rw [← Subgroup.orderOf_mk x hxH]; exact hx2
  have hE : IsElemAbelian 2 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · change (a : G) * b = b * a
      obtain ⟨m, hm⟩ := a.2
      obtain ⟨n, hn⟩ := b.2
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow_self x m n).eq
    · rintro _ ⟨n, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo,
        pow_orderOf_eq_one, one_zpow]
  have h1 := hA.2.2 _ (Subgroup.zpowers_le.mpr hxH) hE
  rw [Nat.card_zpowers, hxo] at h1
  intro hbot
  have hA0 : A ≤ ⊥ := by
    rw [← hbot]
    exact GammaExtra.le_thompsonJ hA
  rw [le_bot_iff] at hA0
  rw [hA0, Subgroup.card_bot] at h1
  omega

namespace Hyp331

theorem exists_involution_tC (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTC : tC L T ≠ ⊥) : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ z ^ 2 = 1 ∧
      z ∈ Subgroup.centralizer (L : Set G) ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  obtain ⟨c, hcC, hc1, hcT⟩ := exists_mem_centralizer_of_normal hT2 inf_le_left
    (le_normalizer_tC hTL) hTC
  obtain ⟨k, hk⟩ := (hT2.to_le (inf_le_left : tC L T ≤ T)) ⟨c, hcC⟩
  have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hc1 (orderOf_eq_one_iff.mp (by simpa using hm))
  set z := c ^ 2 ^ (m - 1) with hz
  have hdvd : 2 ^ (m - 1) ∣ orderOf c := by
    rw [hm]
    exact Nat.pow_dvd_pow 2 (Nat.sub_le m 1)
  have hzord : orderOf z = 2 := by
    rw [hz, orderOf_pow_of_dvd (by positivity) hdvd, hm]
    rw [show m = m - 1 + 1 by omega, pow_succ]
    simp
  have hzC : z ∈ tC L T := (tC L T).pow_mem hcC _
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := Subgroup.pow_mem _ hcT _
  have hz2 : z ^ 2 = 1 := by
    rw [← hzord]
    exact pow_orderOf_eq_one z
  refine ⟨z, Subgroup.subset_closure ⟨⟨(Subgroup.mem_inf.mp hzC).1, hzT⟩, hz2⟩, ?_, hz2,
    (Subgroup.mem_inf.mp hzC).2, hzT⟩
  intro h1
  rw [h1, orderOf_one] at hzord
  omega

end Hyp331

theorem stmt3_3_25_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14) (h24 : Stmt3_3_24)
    (hθ : Fact3_3_25Theta) (hXS3 : Fact3_3_25XS3) (hHat : Insp3_3_25Hat)
    (hThree : Insp3_3_25Three) : Stmt3_3_25 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hodd : ∀ d ∈ D, Odd (orderOf d) := fun d hdD => by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVe : IsElemAbelian 2 (vPlus L T) := hred.2.1
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hVT : vPlus L T ≤ T := hVQ.trans hQT
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hLTV
  have hCV : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hVne : vPlus L T ≠ ⊥ := by
    intro hb'
    apply h.not_L_le_centralizer h38 h39
    rw [hb']
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  set Z := quasithinOmegaOneCenter T with hZdef
  set X := oTwoUpper (L ⊓ Subgroup.centralizer (Z : Set G)) with hXdef
  set R := pCoreOf 2 (X ⊔ T) with hRdef
  have hXL : X ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hTsyl : IsSylowTwoOf T (X ⊔ T) :=
    ⟨le_sup_right, hT2, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow le_sup_right⟩
  have hRT : R ≤ T := pCoreOf_le_of_isSylowTwoOf hTsyl
  have hRLT : R ≤ L ⊔ T :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_right hXL T)
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    (sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQR : qL L T ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right) hXTN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hX3 : (IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
      IsLnBlock L 3) → ∀ x ∈ L ⊓ Subgroup.centralizer (Z : Set G), Odd (orderOf x) →
      x ^ 3 = 1 := by
    intro hb x hx hxo
    obtain ⟨e⟩ := hXS3 G T M L D h hTL hb
    have hxX : x ∈ X := mem_oTwoUpper_of_odd hx hxo
    have hxXT : x ∈ X ⊔ T := Subgroup.mem_sup_left hxX
    have hS6 : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide
    have h1 : e (QuotientGroup.mk ((⟨x, hxXT⟩ : ↥(X ⊔ T)) ^ 6)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, hS6]
    have h2 : (⟨x, hxXT⟩ : ↥(X ⊔ T)) ^ 6 ∈ CFSG.pCore 2 ↥(X ⊔ T) := by
      rw [← QuotientGroup.eq_one_iff]
      exact e.injective (h1.trans (map_one e).symm)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(X ⊔ T))) ⟨_, h2⟩
    have hk' : x ^ (6 * 2 ^ k) = 1 := by
      have := congrArg (fun w => ((w : ↥(X ⊔ T)) : G)) (congrArg Subtype.val hk)
      simpa [pow_mul] using this
    have hdvd : orderOf x ∣ 3 * 2 ^ (k + 1) := by
      rw [show 3 * 2 ^ (k + 1) = 6 * 2 ^ k by rw [pow_succ]; ring]
      exact orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf x) (2 ^ (k + 1)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (Nat.not_even_iff_odd.mpr hxo ∘ (even_iff_two_dvd.mpr))).symm
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)
  have part2 : tC L T ≠ ⊥ → ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      D ≤ Subgroup.normalizer (X : Set G) ∧ D ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ R → L ⊔ T ≤ Subgroup.normalizer (R₀ : Set G) →
        ¬ D ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro hTC hPSL
    have hblock : IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L := by
      rcases h24 G T M L D h with hA | hH | hG | hL3
      · exact Or.inl hA
      · exact Or.inr (Or.inl hH)
      · exact Or.inr (Or.inr hG)
      · exact absurd (h.isPSL_of_isLnBlock h38 h39 hTL hL3) hPSL
    have hblock' : IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
        IsLnBlock L 3 := by
      rcases hblock with hA | hH | hG
      · exact Or.inl hA
      · exact Or.inr (Or.inl hH)
      · exact Or.inr (Or.inr (Or.inl hG))
    obtain ⟨z, hzZ, hz1, hz2, hzL, hzT⟩ := h.exists_involution_tC hTL hTC
    have hCM : Subgroup.centralizer (Z : Set G) ≤ M := by
      have hle : Subgroup.centralizer (Z : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ)
      refine hle.trans (h.toSetup331.le_of_pCoreOf_ne_bot h38 h39 ?_ ?_)
      · refine sup_le (fun l hl => ?_) (fun t ht => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hzL l hl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hzT t ht)
      · intro hbot
        have hzP : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
          refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
            (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ?_ ?_
          · intro y hy
            rw [Subgroup.mem_normalizer_iff]
            intro w
            have hyz : y * z = z * y := (Subgroup.mem_centralizer_singleton_iff.mp hy)
            have hc : ∀ n : ℤ, y * z ^ n * y⁻¹ = z ^ n := fun n => by
              rw [(Commute.zpow_right hyz n).eq]
              group
            constructor
            · rintro ⟨n, rfl⟩
              exact ⟨n, (hc n).symm⟩
            · rintro ⟨n, hn⟩
              have hn' : z ^ n = y * w * y⁻¹ := hn
              refine ⟨n, ?_⟩
              calc z ^ n = y⁻¹ * (y * z ^ n * y⁻¹) * y := by group
                _ = y⁻¹ * (y * w * y⁻¹) * y := by rw [hc n, hn']
                _ = w := by group
          · refine IsPGroup.of_card (n := 1) ?_
            rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
        rw [hbot] at hzP
        exact hz1 ((Subgroup.mem_bot).mp (hzP (Subgroup.mem_zpowers z)))
    have hθX : ∀ y ∈ Subgroup.centralizer (Z : Set G), y ^ 3 = 1 → y ∈ X := by
      intro y hy hy3
      by_cases hy1 : y = 1
      · rw [hy1]
        exact X.one_mem
      have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
      have hyL : y ∈ L := hθ G T M L h.toSetup331 hML hblock y (hCM hy) hyo
      exact mem_oTwoUpper_of_odd ⟨hyL, hy⟩ (by rw [hyo]; decide)
    have hDX' : ∀ d ∈ D, ∀ y ∈ X, d * y * d⁻¹ ∈ X := by
      intro d hdD y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        have hx3 := hX3 hblock' x hx.1 hx.2
        refine hθX _ (conj_mem_centralizer_omegaOneCenter (h.DN hdD) hx.1.2) ?_
        rw [conj_pow, hx3, mul_one, mul_inv_cancel]
      | one => simp
      | mul a b _ _ iha ihb => simpa [mul_assoc] using X.mul_mem iha ihb
      | inv a _ ih => simpa [mul_assoc] using X.inv_mem ih
    have hDX : D ≤ Subgroup.normalizer (X : Set G) := by
      intro d hdD
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨hDX' d hdD y, fun hy => ?_⟩
      have := hDX' d⁻¹ (D.inv_mem hdD) _ hy
      simpa [mul_assoc] using this
    have hDR : D ≤ Subgroup.normalizer (R : Set G) := by
      intro d hdD
      have h1 : (X ⊔ T).map (MulAut.conj d).toMonoidHom = X ⊔ T := by
        rw [Subgroup.map_sup, A38.map_conj_eq_iff.mpr (hDX hdD),
          A38.map_conj_eq_iff.mpr (h.DN hdD)]
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (X ⊔ T)
        (A38.map_conj_eq_iff.mp h1)
    refine ⟨hDX, hDR, fun R₀ hR₀ hR₀R hLT => ?_⟩
    exact h.not_le_normalizer h38 h39 hR₀ (hR₀R.trans hRLT) hLT
  have part1 : IsAltBlockType L 6 ∨ IsG2Block L ∨ IsLnBlock L 3 := by
    rcases h24 G T M L D h with hA | hH | hG | hL3
    · exact Or.inl hA
    · exfalso
      obtain ⟨ha, hb, hc⟩ := hHat G T M L D h hTL hH
      have hPSL : ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := by
        intro hP
        have h1 := h.card_autOn_dvd hTL
        rw [Vol2.Ch11.SecA.card_of_isPSL (by norm_num) hP,
          Vol2.Ch11.SecA.card_of_isHat hH.2.1, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin] at h1
        revert h1
        decide
      have hTC : tC L T = ⊥ := by
        by_contra hTC
        obtain ⟨-, hDR, hno⟩ := part2 hTC hPSL
        have hAQ : ∀ A : Subgroup G, IsMaxElemAbelian R A ↔ IsMaxElemAbelian (qL L T) A := by
          intro A
          constructor
          · intro hA
            exact ⟨ha A hA, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans hQR) hBe⟩
          · intro hA
            refine ⟨hA.1.trans hQR, hA.2.1, fun B hB hBe => ?_⟩
            obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian R
            exact (hA₀.2.2 B hB hBe).trans (hA.2.2 A₀ (ha A₀ hA₀) hA₀.2.1)
        have hQ2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
        have hRne : R ≠ ⊥ := fun hb' => h.toSetup331.pCoreOf_ne_bot (le_bot_iff.mp (by
          rw [← hb']
          exact hQR))
        refine hno (thompsonJ R) (thompsonJ_ne_bot' hQ2 hRne)
          (iSup₂_le fun A hA => hA.1) (fun g hg => ?_) (fun d hdD => ?_)
        · refine mem_normalizer_thompsonJ fun A hA => ?_
          have h1 := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr ((hAQ A).mp hA)
          rw [A38.map_conj_eq_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg)] at h1
          exact (hAQ _).mpr h1
        · refine mem_normalizer_thompsonJ fun A hA => ?_
          have h1 := (isMaxElemAbelian_map_mulEquiv (MulAut.conj d)).mpr hA
          rwa [A38.map_conj_eq_iff.mpr (hDR hdD)] at h1
      have hVQ' := hb hTC
      obtain ⟨h1, h2, h3⟩ := hc hVQ'
      have hCV' : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = vPlus L T := by rw [hCV, hVQ']
      obtain ⟨hVmax, huniq⟩ := unique_of_offenders hVe hVT hTV hCV' h1 h2 h3
      have hDV : D ≤ Subgroup.normalizer (vPlus L T : Set G) := fun d hdD =>
        mem_normalizer_of_odd_of_unique hVmax huniq (h.DN hdD) (hodd d hdD)
      exact h.not_le_normalizer h38 h39 hVne (hVT.trans le_sup_right) hLTV hDV
    · exact Or.inr (Or.inl hG)
    · exact Or.inr (Or.inr hL3)
  have part3 : tC L T = ⊥ → vPlus L T = qL L T ∨ IsAltBlockType L 6 := by
    intro hTC
    by_contra hcon
    push Not at hcon
    obtain ⟨hVQne, hnA6⟩ := hcon
    have hblock : IsG2Block L ∨ IsLnBlock L 3 := by
      rcases part1 with hA | hG | hL3
      · exact absurd hA hnA6
      · exact Or.inl hG
      · exact Or.inr hL3
    have hshort : IsShort2 L := by
      rcases hblock with hG | hL3
      · exact hG.1
      · exact hL3.1
    obtain ⟨-, ha, hb, hc⟩ := hThree G T M L D h hTL hblock hTC hVQne
      (h.isFFModule h38 h39)
    have hFQ := h.frattini_qL_le_tC h38 h39 hshort hTL
    rw [hTC] at hFQ
    have hF : frattini ↥(qL L T) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (qL L T).subtype_injective).mp (le_bot_iff.mp hFQ)
    have hQe : IsElemAbelian 2 (qL L T) :=
      isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF
    have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
      have := hQe.1
      exact setLike_mul_comm ha hb
    have hTQ : T ≤ Subgroup.normalizer (qL L T : Set G) :=
      le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hCQ : T ⊓ Subgroup.centralizer (qL L T : Set G) = qL L T := by
      refine le_antisymm (fun x hx => ?_) (le_inf hQT fun y hy =>
        Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz y hy)
      rw [← hCV]
      exact ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hx.2⟩
    obtain ⟨hQmax, huniq⟩ := unique_of_offenders hQe hQT hTQ hCQ ha hb hc
    have hDQ : D ≤ Subgroup.normalizer (qL L T : Set G) := fun d hdD =>
      mem_normalizer_of_odd_of_unique hQmax huniq (h.DN hdD) (hodd d hdD)
    exact h.not_le_normalizer h38 h39 h.toSetup331.pCoreOf_ne_bot
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      hDQ
  exact ⟨part1, part2, part3⟩

end CFSG.Quasithin.H13
