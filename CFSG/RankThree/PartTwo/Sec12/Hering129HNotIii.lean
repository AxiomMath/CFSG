module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GNotIii
public import CFSG.RankThree.PartTwo.Sec12.Hering129HC9
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLEnd
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec12.ONanKS128
public import CFSG.RankThree.PartTwo.Sec12.Hering129Setup

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Types

variable {G : Type} [Group G] [Finite G]

@[expose] def Typ129IIIcMinus (A : Subgroup G) (c : G) (L Y : Subgroup G) (x : G) : Prop :=
  (∃ q : TauCeti.PrimePower, Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card) ∧
  ((∃ (p e : ℕ) (_ : Fact p.Prime), Sec4.IsoLThreePi (Y ⧸ CFSG.pCore 2 Y) p e) ∨
    ∃ (q₀ : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q₀).Valid),
      Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q₀, hq⟩).Group)) ∧
  Subgroup.center (Y ⧸ CFSG.pCore 2 Y) = ⊥ ∧
  ∃ E : Subgroup G, Late.IsE27 E ∧ E = Subgroup.zpowers x ⊔ (E ⊓ Y) ∧ c ∈ E ⊓ Y ∧
    ¬ Y ⊓ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
    (∃ Z U : Subgroup G, E ⊔ A = Z ⊔ U ∧ Z ⊓ U = ⊥ ∧ Nat.card Z = 3 ∧
      (∀ z ∈ Z, ∀ u ∈ U, z * u = u * z) ∧ Sec4.IsHeisThree U) ∧
    Nonempty (Sec4.autIn (Y ⊔ A) E ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

end Types

namespace Hering129G

variable {G : Type} [Group G] [Finite G]

theorem false_of_transitive_minus (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G)
    {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c) (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hc3 : orderOf c = 3) (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (haC : a ∉ Sec4.thetaQuotCentralizer L) (haL : a ∈ L)
    {K E F : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (haK : a ∉ K) (hFK : F ≤ K)
    (hE : Late.IsE27 E) (hEdec : E = Subgroup.zpowers a ⊔ F) (hF9 : Nat.card F = 9)
    (hcF : c ∈ F)
    (hT : ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 → ∃ m ∈ Subgroup.normalizer (E : Set G),
      m * a = a * m ∧ m * u * m⁻¹ = v)
    (hC9 : E ≤ lcBar c L → Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hN : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haE : a ∈ E := hEdec ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have ha3 : a ^ 3 = 1 := hE.1.2 a haE
  have hFE : F ≤ E := hEdec ▸ le_sup_right
  have hcE : c ∈ E := hFE hcF
  have hEc : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hEp : IsPGroup 3 E := hE.isPGroup
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hcL hLc
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    mem_normalizer_zpowers_of_commute (hEc x hx c hcE)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hG hc3 hL hEp hEH
  have haF : a ∉ F := fun h1 => haK (hFK h1)
  obtain ⟨f₀, hf₀F, hf₀c⟩ : ∃ f₀ ∈ F, f₀ ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show F ≤ Subgroup.zpowers c from hcon)
    rw [hF9, Nat.card_zpowers, hc3] at this
    omega
  have hBp : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := hEp.to_le inf_le_left
  have hdvd : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨n, hn3, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases n
  ·
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hc1 (by simpa [hn] using (Subgroup.mem_inf.mpr ⟨hcE, hcC⟩ :
      c ∈ E ⊓ Sec4.thetaQuotCentralizer L))
  ·
    rw [pow_one] at hn
    obtain ⟨y, hyN, hyc, hya, hya1, hyF⟩ :=
      KS128NotHJSL.exists_move ks128TypeCMove hL hSL hcL hc1 hcC hE hEN hcE haE haL haC hn
    have hFW : ∀ f ∈ F, f ∉ Subgroup.zpowers c →
        f ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
      intro f hfF hfc hfW
      obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup (hEc a haE c hcE) hfW
      have hcj : (c ^ j)⁻¹ ∈ F := F.inv_mem (F.zpow_mem hcF j)
      rcases KS128NotHJSL.zpow_eq_one_or_eq_or_eq_inv ha3 i with h0 | h1 | h2
      · exact hfc (by rw [h0, one_mul]; exact Subgroup.zpow_mem_zpowers c j)
      · apply haF
        have := F.mul_mem hfF hcj
        rwa [h1, mul_inv_cancel_right] at this
      · apply haF
        have := F.inv_mem (F.mul_mem hfF hcj)
        rwa [h2, mul_inv_cancel_right, inv_inv] at this
    obtain ⟨hh, hhE, hhc⟩ := KS128NotHJSL.exists_conj_eq_of_moves hEc haE ha3 hFE hcF hc1 hT hyN
      hyc hya hya1 (fun f hfF hfc => hyF f (hFE hfF) (hFW f hfF hfc)) hf₀F hf₀c
    have hEdec' : ∀ e ∈ E, ∃ k : ℤ, ∃ f ∈ F, e = a ^ k * f :=
      exists_zpow_mul_of_mem_sup_zpowers_sup hEdec fun f hf => hEc a haE f (hFE hf)
    have hEC := KS128NotHJSL.le_thetaQuotCentralizer_of_conj_eq hK haK hFK hFE hEdec' hEN hL hcL
      hcC hhE hhc
    exact haC (hEC haE)
  ·
    have hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 := by
      rw [hn]
      norm_num
    have hEsup : Subgroup.zpowers a ⊔ (E ⊓ Sec4.thetaQuotCentralizer L) = E :=
      eq_of_card_nine_lt hE.2 (sup_le (Subgroup.zpowers_le.mpr haE) inf_le_left) le_sup_right hB9
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (fun h1 => haC h1.2)
    have hElc : E ≤ lcBar c L := by
      rw [← hEsup]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · have := KS128NotHJTC.mul_mem_lcBar hL haL (Subgroup.one_mem _) (Subgroup.one_mem _)
        simpa using this
      · intro x hx
        have := KS128NotHJTC.mul_mem_lcBar hL L.one_mem hx.2 (hEH hx.1)
        simpa using this
    exact hN (hC9 hElc hB9)
  ·
    have hEC : E ⊓ Sec4.thetaQuotCentralizer L = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hn, hE.2]; norm_num)
    have hmem : a ∈ E ⊓ Sec4.thetaQuotCentralizer L := by rw [hEC]; exact haE
    exact haC hmem.2

end Hering129G

section Step

variable {G : Type} [Group G] [Finite G]

theorem not_typ129IIIcMinus_of_mem_L (h45 : Sec4.Item4_5) (h125 : Item125BarC9)
    {A L K S : Subgroup G} {c b a : G}
    (cfg : Cfg129 G A c L b a K S) (hty : GTwoType129 L K) {x : G} (hxD : x ∈ D129 a b)
    (hxb : x ∉ Subgroup.zpowers b) (hxL : x ∈ L) {Y : Subgroup G} (hY : Core129 A c x Y) :
    ¬ Typ129IIIcMinus A c L Y x := by
  rintro ⟨-, -, hZY, E, hE, hEdec, hcEY, hH, -, hΓ⟩
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hxC : x ∉ Sec4.thetaQuotCentralizer L := by
    intro hxC
    obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hAc a haA b hbA) hxD
    have hai : a ^ i ∈ Sec4.thetaQuotCentralizer L := by
      have h1 : a ^ i = x * (b ^ j)⁻¹ := by rw [hij]; group
      rw [h1]
      exact Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ (Subgroup.zpow_mem _ cfg.hb.2 j))
    rw [Sec4.zpow_emod_three ha3 i] at hai
    have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hi with h | h | h
    · apply hxb
      rw [hij, Sec4.zpow_emod_three ha3 i, h, zpow_zero, one_mul]
      exact Subgroup.zpow_mem_zpowers b j
    · rw [h, zpow_one] at hai
      exact haB hai
    · rw [h] at hai
      apply haB
      have h2 : a = (a ^ (2 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul]
        have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
        calc a = a ^ (3 : ℤ) * a := by rw [h3, one_mul]
          _ = a ^ (4 : ℤ) := by rw [← zpow_add_one]; norm_num
          _ = _ := by norm_num
      rw [h2]
      exact Subgroup.zpow_mem _ hai 2
  obtain ⟨q, hq, -⟩ := hty
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) := ⟨q.card, hq⟩
  have hcL := hstd.mem_L
  have hc1 := hstd.ne_one
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hstd.mem_A) hc1
  have hYx : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY.1
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hxY : x ∉ Y := by
    intro hxY
    have hc : QuotientGroup.mk' (CFSG.pCore 2 Y) ⟨x, hxY⟩ ∈
        Subgroup.center (Y ⧸ CFSG.pCore 2 Y) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        have hg : (g : G) * x = x * (g : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hYx g.2)
        change ((g * ⟨x, hxY⟩ : Y) : Y ⧸ CFSG.pCore 2 Y) =
          ((⟨x, hxY⟩ * g : Y) : Y ⧸ CFSG.pCore 2 Y)
        rw [show (g * ⟨x, hxY⟩ : Y) = ⟨x, hxY⟩ * g from Subtype.ext hg]
    rw [hZY, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    have hp : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨⟨x, hxY⟩, hc⟩
    have hord : orderOf (⟨x, hxY⟩ : Y) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hx3 hx1
    have hk' : orderOf (⟨x, hxY⟩ : Y) = 2 ^ k :=
      (Subgroup.orderOf_coe (⟨⟨x, hxY⟩, hc⟩ : CFSG.pCore 2 Y)).trans hk
    have h3 : (3 : ℕ) = 2 ^ k := hord.symm.trans hk'
    have : Even (2 ^ k) ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact Or.inr h0
      · exact Or.inl (Nat.even_pow.mpr ⟨even_two, h0.ne'⟩)
    rcases this with h | h
    · rw [← h3] at h
      exact absurd h (by decide)
    · rw [h] at h3
      exact absurd h3 (by norm_num)
  have hxE : x ∈ E := hEdec ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hxF : x ∉ E ⊓ Y := fun h => hxY h.2
  have hF9 : Nat.card (E ⊓ Y : Subgroup G) = 9 := Hering129G.card_eq_nine_of_sup hE hEdec hxF hx3
  have hEc : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hxFc : ∀ f ∈ E ⊓ Y, x * f = f * x := fun f hf => hEc x hxE f hf.1
  have hAx : A ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy x hxA)
  have hMx : ∀ m ∈ Y ⊔ A, m * x = x * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hYx hAx) hm)
  have hMY : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2.1
  have hMF : ∀ m ∈ Y ⊔ A, m ∈ Subgroup.normalizer (E : Set G) →
      ∀ f ∈ E ⊓ Y, m * f * m⁻¹ ∈ E ⊓ Y := fun m hm hmE f hf =>
    ⟨(Subgroup.mem_normalizer_iff.mp hmE f).mp hf.1,
      (Subgroup.mem_normalizer_iff.mp (hMY hm) f).mp hf.2⟩
  have hT := Hering129G.exists_conj_of_autIn_sl23 hxE inf_le_left hEdec hF9 hMx hMF hxFc hΓ
  exact Hering129G.false_of_transitive_minus h45 hstd.toTheoremFourHyp
    hstd.mem_thetaComponentsAt hcL hc1 hc3 hSL hxC hxL hY.1 hxY inf_le_right hE hEdec hF9 hcEY
    (fun u hu hu1 v hv hv1 => by
      obtain ⟨m, hm, hmN, hmuv⟩ := hT u hu hu1 v hv hv1
      exact ⟨m, hmN, hMx m hm, hmuv⟩)
    (fun hElc hn9 => h125 G A c L hstd (Or.inl hSL) E hE hElc hcEY.1 hn9)
    (fun h => hH (inf_le_right.trans h))

theorem gap129NotIiiLcMinus_of (h45 : Sec4.Item4_5) (h125 : Item125BarC9) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
      (K S : Subgroup G), Cfg129 G A c L b a K S → GTwoType129 L K →
      ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b → x ∈ L →
        ∀ Y : Subgroup G, Core129 A c x Y → ¬ Typ129IIIcMinus A c L Y x :=
  fun G _ _ A c L b a K S cfg hty x hxD hxb hxL Y hY =>
    not_typ129IIIcMinus_of_mem_L h45 h125 cfg hty hxD hxb hxL hY

end Step

end CFSG.RankThree.PartTwo.Sec12
