module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryCav
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImageOrder
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartImage
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoNodeBasics
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G]

theorem ggQ2cn_exists_mul_zpow {X : Subgroup G} {u : G}
    (huX : X ≤ Subgroup.centralizer ({u} : Set G)) {g : G}
    (hg : g ∈ X ⊔ Subgroup.zpowers u) : ∃ c ∈ X, ∃ n : ℤ, g = c * u ^ n := by
  have hcomm : ∀ c ∈ X, ∀ n : ℤ, u ^ n * c = c * u ^ n := fun c hc n =>
    ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (huX hc)) n).eq).symm
  let H : Subgroup G :=
    { carrier := {g | ∃ c ∈ X, ∃ n : ℤ, g = c * u ^ n}
      mul_mem' := by
        rintro _ _ ⟨c₁, hc₁, n₁, rfl⟩ ⟨c₂, hc₂, n₂, rfl⟩
        refine ⟨c₁ * c₂, X.mul_mem hc₁ hc₂, n₁ + n₂, ?_⟩
        rw [zpow_add, show c₁ * u ^ n₁ * (c₂ * u ^ n₂) = c₁ * (u ^ n₁ * c₂) * u ^ n₂ by
          simp only [mul_assoc], hcomm c₂ hc₂ n₁]
        simp only [mul_assoc]
      one_mem' := ⟨1, X.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨c, hc, n, rfl⟩
        refine ⟨c⁻¹, X.inv_mem hc, -n, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, hcomm c⁻¹ (X.inv_mem hc) (-n)] }
  have hXH : X ≤ H := fun c hc => ⟨c, hc, 0, by simp⟩
  have huH : u ∈ H := ⟨1, X.one_mem, 1, by simp⟩
  exact (sup_le hXH (Subgroup.zpowers_le.mpr huH)) hg

theorem ggQ2cn_conj_mem {p : ℕ} {Bs X : Subgroup G} {u : G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hEA : IsElemAbelian p Bs)
    (hOm : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (huX : X ≤ Subgroup.centralizer ({u} : Set G)) (huB : u ∈ Bs)
    (hsup : Bs ≤ X ⊔ Subgroup.zpowers u) {k : G} (hk : k ∈ X)
    (hA : X.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ ∈
      Subgroup.normalizer ((ggGamma X hN).range : Set (MulAut X)))
    {b : G} (hb : b ∈ Bs) : k * b * k⁻¹ ∈ Bs := by
  have hcommX : ∀ c ∈ X, ∀ n : ℤ, u ^ n * c = c * u ^ n := fun c hc n =>
    ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (huX hc)) n).eq).symm
  have hdec : ∀ g ∈ Bs, ∃ c ∈ X, c ∈ Bs ∧ ∃ n : ℤ, g = c * u ^ n := by
    intro g hg
    obtain ⟨c, hc, n, rfl⟩ := ggQ2cn_exists_mul_zpow huX (hsup hg)
    refine ⟨c, hc, ?_, n, rfl⟩
    have h := Bs.mul_mem hg (Bs.zpow_mem huB (-n))
    rwa [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] at h
  obtain ⟨c, hcX, hcB, n, rfl⟩ := hdec b hb
  set ρ := X.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ with hρ
  have hmem : ρ * ggGamma X hN ⟨c, hcB⟩ * ρ⁻¹ ∈ (ggGamma X hN).range :=
    (Subgroup.mem_normalizer_iff.mp hA _).mp ⟨⟨c, hcB⟩, rfl⟩
  obtain ⟨⟨b', hb'⟩, hb'eq⟩ := hmem
  obtain ⟨c', hc'X, hc'B, n', hb'c⟩ := hdec b' hb'
  obtain ⟨a, ha⟩ : ∃ a : G, a = k * c * k⁻¹ := ⟨_, rfl⟩
  have haX : a ∈ X := ha ▸ X.mul_mem (X.mul_mem hk hcX) (X.inv_mem hk)
  have hact : ∀ l ∈ X, c' * l * c'⁻¹ = a * l * a⁻¹ := by
    intro l hl
    have h1 := congrArg (fun φ : MulAut X => ((φ ⟨l, hl⟩ : X) : G)) hb'eq
    have hinv : ρ⁻¹ = X.normalizerMonoidHom ⟨k⁻¹, Subgroup.le_normalizer (X.inv_mem hk)⟩ := by
      rw [hρ, ← map_inv]
      rfl
    simp only [MulAut.mul_apply, hinv] at h1
    change b' * l * b'⁻¹ = k * (c * (k⁻¹ * l * k⁻¹⁻¹) * c⁻¹) * k⁻¹ at h1
    have hul : u ^ n' * l * (u ^ n')⁻¹ = l := by
      rw [hcommX l hl n', mul_assoc, mul_inv_cancel, mul_one]
    rw [hb'c, mul_inv_rev, show c' * u ^ n' * l * ((u ^ n')⁻¹ * c'⁻¹) =
      c' * (u ^ n' * l * (u ^ n')⁻¹) * c'⁻¹ by simp only [mul_assoc], hul] at h1
    rw [h1, ha]
    group
  obtain ⟨w, hw⟩ : ∃ w : G, w = a⁻¹ * c' := ⟨_, rfl⟩
  have hwX : w ∈ X := hw ▸ X.mul_mem (X.inv_mem haX) hc'X
  have hwC : ∀ l ∈ X, l * w = w * l := by
    intro l hl
    have h := hact l hl
    rw [hw]
    calc l * (a⁻¹ * c') = a⁻¹ * (a * l * a⁻¹) * c' := by group
      _ = a⁻¹ * (c' * l * c'⁻¹) * c' := by rw [h]
      _ = a⁻¹ * c' * l := by group
  have hpow_c : ∀ g ∈ Bs, g ^ p = 1 := fun g hg => hEA.2 g hg
  have hwp : w ^ p = 1 := by
    have hca : c' = a * w := by rw [hw]; group
    have hcomm : Commute a w := hwC a haX
    have hap : a ^ p = 1 := by
      rw [ha, conj_pow, hpow_c c hcB, mul_one, mul_inv_cancel]
    have h := hpow_c c' hc'B
    rw [hca, hcomm.mul_pow, hap, one_mul] at h
    exact h
  have hwB : w ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨c'', hc''X, -, n'', rfl⟩ := hdec g hg
    have h1 : Commute c'' w := hwC c'' hc''X
    have h2 : Commute (u ^ n'') w := hcommX w hwX n''
    exact (h1.mul_left h2).eq
  have hwBs : w ∈ Bs := hOm w hwB hwp
  have hkb : k * (c * u ^ n) * k⁻¹ = c' * w⁻¹ * u ^ n := by
    have hku : k * u ^ n = u ^ n * k := (hcommX k hk n).symm
    have haw : a = c' * w⁻¹ := by rw [hw]; group
    calc k * (c * u ^ n) * k⁻¹ = k * c * (k⁻¹ * (k * u ^ n)) * k⁻¹ := by group
      _ = k * c * (k⁻¹ * (u ^ n * k)) * k⁻¹ := by rw [hku]
      _ = a * u ^ n := by rw [ha]; group
      _ = c' * w⁻¹ * u ^ n := by rw [haw]
  rw [hkb]
  exact Bs.mul_mem (Bs.mul_mem hc'B (Bs.inv_mem hwBs)) (Bs.zpow_mem huB n)

theorem ggQ2_conj_mem_of_le_sup_zpowers {p : ℕ} {Bs X : Subgroup G} {u : G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hEA : IsElemAbelian p Bs)
    (hOm : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (huX : X ≤ Subgroup.centralizer ({u} : Set G)) (huB : u ∈ Bs)
    (hsup : Bs ≤ X ⊔ Subgroup.zpowers u) {k : G} (hk : k ∈ X)
    (hA : X.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ ∈
      Subgroup.normalizer ((ggGamma X hN).range : Set (MulAut X))) :
    k ∈ Subgroup.normalizer (Bs : Set G) := by
  have hA' : X.normalizerMonoidHom ⟨k⁻¹, Subgroup.le_normalizer (X.inv_mem hk)⟩ ∈
      Subgroup.normalizer ((ggGamma X hN).range : Set (MulAut X)) := by
    have h := Subgroup.inv_mem _ hA
    rw [← map_inv] at h
    exact h
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => ggQ2cn_conj_mem hN hEA hOm huX huB hsup hk hA hb, fun hb => ?_⟩
  have h := ggQ2cn_conj_mem hN hEA hOm huX huB hsup (X.inv_mem hk) hA' hb
  rwa [show k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b by group] at h

theorem ggQ2_exists_overGamma_of_le_sup_zpowers {p : ℕ} {Bs X J : Subgroup G} {u : G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hEA : IsElemAbelian p Bs)
    (hOm : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (huX : X ≤ Subgroup.centralizer ({u} : Set G)) (huB : u ∈ Bs)
    (hsup : Bs ≤ X ⊔ Subgroup.zpowers u) (hJX : J ≤ X) {a : MulAut ↥(ggGamma X hN).range}
    (ha : a ∈ ggAutomizer (ggGamma X (hJX.trans Subgroup.le_normalizer)).range
      (ggGamma X hN).range) :
    ∃ c ∈ ggAutomizer J Bs, GGOverGamma hN c a := by
  obtain ⟨t, htJ, htN, hta⟩ := mem_ggAutomizer_iff.mp ha
  obtain ⟨j₀, rfl⟩ := MonoidHom.mem_range.mp htJ
  have hjX : (j₀ : G) ∈ X := hJX j₀.property
  have hjB : (j₀ : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    ggQ2_conj_mem_of_le_sup_zpowers hN hEA hOm huX huB hsup hjX htN
  refine ⟨ggConjAut Bs hjB, ggConjAut_mem_ggAutomizer j₀.property hjB, ?_⟩
  intro b
  apply Subtype.ext
  rw [hta]
  exact (ggGamma_conj_normalizer X hN ⟨j₀, Subgroup.le_normalizer hjX⟩ b
    (ggConjAut Bs hjB b).property).symm

theorem ggQ2_card_automizer_image_dvd_of_le_sup_zpowers [Finite G] {p : ℕ}
    {Bs X J : Subgroup G} {u : G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hEA : IsElemAbelian p Bs)
    (hOm : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (huX : X ≤ Subgroup.centralizer ({u} : Set G)) (huB : u ∈ Bs)
    (hsup : Bs ≤ X ⊔ Subgroup.zpowers u) (hJX : J ≤ X) :
    Nat.card (ggAutomizer ((J.subgroupOf X).map (MulAut.conj : X →* MulAut X))
      (ggGamma X hN).range) ∣ Nat.card (ggAutomizer J Bs) := by
  rw [← QTwoCav.gamma_j_range hJX]
  exact QTwoCav.card_automizer_image_dvd hN fun _ ha =>
    ggQ2_exists_overGamma_of_le_sup_zpowers hN hEA hOm huX huB hsup hJX ha

theorem ggQ2_cav_nbr_twA_of_heart
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hIDA : GGInnerDiagAll p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {N : ℕ} (h7 : 7 ≤ N) (hrow : GGQ2S08RowTwA p N K J)
    (M : GGQ2LDatum p Bs K y) (hM : M.HeartShape) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨labX, labJ, hmX, hmJ, hJt, hXt, hrk, hn, hpd, hpq, hNJ⟩ := hrow
  obtain ⟨lX, hΛX, hhasX, -, -, -, -, -, hEX⟩ := largeEvenMarking_exists_hasLabel hmX
  obtain ⟨lJ, -, hhasJ, -, -, -, -, -, hEJ⟩ := largeEvenMarking_exists_hasLabel hmJ
  subst hEX hEJ
  obtain ⟨tX, rX, nX⟩ := lX
  obtain ⟨tJ, rJ, nJ⟩ := lJ
  dsimp only at hJt hXt hrk hn hpd hpq hNJ hΛX hhasX hhasJ
  subst hJt hXt hrk hn
  have hpd' : p ∣ rJ + 2 + 1 := by simpa only [Nat.add_assoc] using hpd
  have hJLab : GGHasLabel ⟨.twA, rJ + 2 - 2, nX⟩ (J ⧸ Subgroup.center J) := by
    simpa only [Nat.add_sub_cancel] using hhasJ
  obtain ⟨F, hField, hFinite, -, hN, φ, S, hF, hMod, hJ, hS, hdiag⟩ :=
    exists_corank_two_block_of_large_unitary_K_of_cfg hRig hLB hcfg hIDA hnb (by omega)
      (by omega) hpq hpd' hhasX hΛX hJLab
  let : Field F := hField
  let : Finite F := hFinite
  have hEA : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hOm : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hyB : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hyK : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hsup : Bs ≤ K ⊔ Subgroup.zpowers y := M.bstar_le_sup_zpowers_of_heartShape hp2 hN hM
  have hJK : J ≤ K := by
    rw [hJ]
    rintro _ ⟨s, -, rfl⟩
    exact (φ s).property
  have hcomm : ∀ a b : Bs, a * b = b * a := hEA.1.is_comm.comm
  have hexp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (hEA.2 b b.property)
  have hfour := QTwoUnitaryCav.block_image_automizer_four hMod hF hp hp2 hpq (by omega)
    (isElemAbelian_range hcomm hexp (ggGamma K hN)) (ggTorusSelfCent_ggGamma hN hOm)
    hdiag S (by omega)
  have hJeq : (J.subgroupOf K).map (MulAut.conj : K →* MulAut K) =
      ((TableBUE.blockSU (K := F) (n := nX) S).map φ).map (MulAut.conj : K →* MulAut K) := by
    rw [hJ, ← Subgroup.map_map]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [← hJeq] at hfour
  exact hfour.trans (ggQ2_card_automizer_image_dvd_of_le_sup_zpowers hN hEA hOm hyK hyB hsup hJK)

end CFSG.StandardType

end
