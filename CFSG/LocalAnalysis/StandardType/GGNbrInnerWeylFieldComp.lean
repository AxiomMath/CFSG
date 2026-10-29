module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylComp
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Config

variable {G : Type} [Group G] [Finite G]

theorem pow_succ_le_card_range_ggGamma_of_field {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {I F : Set (MulAut R)} (hInn : ∀ g : R, MulAut.conj g ∈ I)
    (hfix : GGTorusLiftFix p r R I F)
    (hBsIF : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F))
    (hnot : ∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) :
    p ^ (r + 1) ≤ Nat.card (ggGamma K hN).range := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  have hyB : y ∈ B := hS.2.1
  have hyp : y ^ p = 1 := hS.1.1.2 y hS.2.1
  have hy1 : y ≠ 1 := hS.2.2.1
  obtain ⟨b, hb, hbI⟩ := hnot
  have hbp : b ^ p = 1 := by simpa using hBs.2 b hb
  have hψ := ggQuotHom_surjective θ
  have hconj : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) (k : K),
      (∀ l : K, g * l * g⁻¹ = k * l * (k : G)⁻¹) →
        ggLAut K θ ⟨g, hg⟩ = MulAut.conj (ggQuotHom θ k) := by
    intro g hg k hk
    ext r'
    obtain ⟨l, rfl⟩ := hψ r'
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ggQuotHom_apply, ggQuotHom_apply,
      ggLAut_apply]
    congr 2
    apply Subtype.ext
    rw [normalizerMonoidHom_coe, hk]
    simp
  have hKC : ∀ g ∈ (K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G),
      ∃ k : K, ∀ l : K, g * l * g⁻¹ = k * l * (k : G)⁻¹ := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact ⟨⟨g, hg⟩, fun l => rfl⟩
      · refine ⟨1, fun l => ?_⟩
        have hg' : g ∈ Subgroup.centralizer (K : Set G) := hg
        rw [Subgroup.mem_centralizer_iff] at hg'
        have := hg' l l.2
        simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
        rw [← this]
        group
    | one => exact ⟨1, fun l => by simp⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨k, hk⟩ := ihg
      obtain ⟨k', hk'⟩ := ihh
      refine ⟨k * k', fun l => ?_⟩
      have e1 := hk' l
      have e2 := hk ⟨(k' : G) * l * (k' : G)⁻¹, by
        exact K.mul_mem (K.mul_mem k'.2 l.2) (K.inv_mem k'.2)⟩
      calc g * h * l * (g * h)⁻¹ = g * (h * l * h⁻¹) * g⁻¹ := by group
        _ = g * ((k' : G) * l * (k' : G)⁻¹) * g⁻¹ := by rw [e1]
        _ = k * ((k' : G) * l * (k' : G)⁻¹) * (k : G)⁻¹ := e2
        _ = ((k * k' : K) : G) * l * ((k * k' : K) : G)⁻¹ := by push_cast; group
    | inv g _ ihg =>
      obtain ⟨k, hk⟩ := ihg
      refine ⟨k⁻¹, fun l => ?_⟩
      have e := hk ⟨(k : G)⁻¹ * l * k, K.mul_mem (K.mul_mem (K.inv_mem k.2) l.2) k.2⟩
      have e' : g * ((k : G)⁻¹ * l * k) * g⁻¹ = l := by rw [e]; group
      calc g⁻¹ * l * g⁻¹⁻¹ = g⁻¹ * (g * ((k : G)⁻¹ * l * k) * g⁻¹) * g := by rw [e']; group
        _ = ((k⁻¹ : K) : G) * l * ((k⁻¹ : K) : G)⁻¹ := by push_cast; group
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hbI
    have : ggLAut K θ ⟨1, hN hb⟩ = MulAut.conj (ggQuotHom θ 1) :=
      hconj 1 (hN hb) 1 (fun l => by simp)
    rw [this]
    exact hInn _
  have hnotin : ∀ g ∈ Subgroup.zpowers b, ∀ (hg : g ∈ Subgroup.normalizer (K : Set G)) (r' : R),
      ggLAut K θ ⟨g, hg⟩ = MulAut.conj r' → g = 1 := by
    intro g hgb hg r' hr'
    by_contra hg1
    have hgp : g ^ p = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgb
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
    have hog : orderOf g = p := orderOf_eq_prime hgp hg1
    have hob : orderOf b = p := orderOf_eq_prime hbp hb1
    have hzeq : Subgroup.zpowers g = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgb)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hog, hob])
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hzeq ▸ Subgroup.mem_zpowers b)
    apply hbI
    have e : (⟨b, hN hb⟩ : Subgroup.normalizer (K : Set G)) = ⟨g, hg⟩ ^ m :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    rw [e, map_zpow, hr', ← map_zpow]
    exact hInn _
  set f := ggGamma K hN ⟨b, hb⟩ with hf
  have hfp : f ^ p = 1 := by
    rw [hf, ← map_pow]
    have : (⟨b, hb⟩ : Bs) ^ p = 1 := Subtype.ext (by simpa using hbp)
    rw [this, map_one]
  have hfF : ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : K,
      φ (ggQuotHom θ l) = ggQuotHom θ (f l) :=
    ⟨ggBeta K θ hN ⟨b, hb⟩, hBsIF b hb, fun l => ggBeta_ggQuotHom K hN θ ⟨b, hb⟩ l⟩
  have hfnI : ¬ ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (f l) := by
    rintro ⟨φ, hφ, hφf⟩
    apply hbI
    have e : φ = ggLAut K θ ⟨b, hN hb⟩ := by
      ext r'
      obtain ⟨l, rfl⟩ := hψ r'
      rw [hφf]
      exact (ggBeta_ggQuotHom K hN θ ⟨b, hb⟩ l).symm
    exact e ▸ hφ
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, hEker, hfU, hfE⟩ := hfix K (ggQuotHom θ) hψ
    (by rw [ker_ggQuotHom]) hK f hfp hfF hfnI
  rw [ker_ggQuotHom] at hEker
  have hbK : ∀ l : K, f l = l → b * l = l * b := by
    intro l hl
    have h1 := congrArg Subtype.val hl
    rw [hf, ggGamma_coe] at h1
    calc b * l = b * l * b⁻¹ * b := by group
      _ = l * b := by rw [h1]
  have hyK : ∀ l ∈ K, l * y = y * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKy hl)
  have hby : b * y = y * b := IsElemAbelian.comm hBs hb (hBBs hyB)
  set EG := E.map K.subtype with hEG
  have hEGab : IsElemAbelian p EG := isElemAbelian_map hE K.subtype
  have hYab : IsElemAbelian p (Subgroup.zpowers y) := isElemAbelian_zpowers hyp
  have hBab : IsElemAbelian p (Subgroup.zpowers b) := isElemAbelian_zpowers hbp
  have hEY : ∀ a ∈ EG, ∀ c ∈ Subgroup.zpowers y, a * c = c * a := by
    rintro _ ⟨e, -, rfl⟩ c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Commute.zpow_right (hyK e e.2) i
  set M1 := EG ⊔ Subgroup.zpowers y with hM1
  have hM1ab : IsElemAbelian p M1 := isElemAbelian_sup hEGab hYab hEY
  have hM1b : M1 ≤ Subgroup.centralizer ({b} : Set G) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hbK e (hfE e he)).symm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hby.symm
  have hMb : ∀ a ∈ M1, ∀ c ∈ Subgroup.zpowers b, a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hM1b ha)) i
  have hMab : IsElemAbelian p (M1 ⊔ Subgroup.zpowers b) := isElemAbelian_sup hM1ab hBab hMb
  have hM1KC : M1 ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
    refine sup_le ((Subgroup.map_subtype_le E).trans le_sup_left) ?_
    rw [Subgroup.zpowers_le]
    exact le_sup_right (a := K) (Subgroup.mem_centralizer_iff.mpr fun l hl => hyK l hl)
  have hdisj1 : Disjoint EG (Subgroup.zpowers y) := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨e, he, rfl⟩ hXe
    have hec : e ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro l
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hXe
      apply Subtype.ext
      show (l : G) * e = e * l
      rw [show (e : G) = y ^ i from hi.symm]
      exact Commute.zpow_right (hyK l l.2) i
    have : e ∈ E ⊓ Subgroup.center K := ⟨he, hec⟩
    rw [hEker, Subgroup.mem_bot] at this
    rw [this]
    rfl
  have hYN : Subgroup.zpowers y ≤ Subgroup.normalizer (EG : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hEY a ha c hc)
  have hcard1 : Nat.card M1 = p ^ (r + 1) := by
    rw [hM1, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hYN hdisj1,
      hEG, ← Nat.card_congr (E.equivMapOfInjective _ K.subtype_injective).toEquiv, hEcard,
      Nat.card_zpowers, orderOf_eq_prime hyp hy1, pow_succ]
  have hdisj2 : Disjoint M1 (Subgroup.zpowers b) := by
    rw [Subgroup.disjoint_def]
    intro g hgM hgb
    obtain ⟨k, hk⟩ := hKC g (hM1KC hgM)
    have hg : g ∈ Subgroup.normalizer (K : Set G) :=
      (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G)))
        (hM1KC hgM)
    exact hnotin g hgb hg _ (hconj g hg k hk)
  have hBN' : Subgroup.zpowers b ≤ Subgroup.normalizer (M1 : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      hMb a ha c hc)
  have hcard : Nat.card (M1 ⊔ Subgroup.zpowers b : Subgroup G) = p ^ (r + 2) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hBN' hdisj2,
      hcard1, Nat.card_zpowers, orderOf_eq_prime hbp hb1, ← pow_succ]
  have hUne : U.map K.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map K.subtype : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have hle : M1 ⊔ Subgroup.zpowers b ≤
      Subgroup.normalizer ((U.map K.subtype : Subgroup G) : Set G) := by
    refine sup_le (sup_le ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)) ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨u, -, rfl⟩ := hg
        exact hyK u u.2)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨u, hu, rfl⟩ := hg
        exact (hbK u (hfU u hu)).symm)
  have hrank : r + 2 ≤ LargeEvenTwoLocalRank p G :=
    le_twoLocalRank hp.one_lt hTL (le_pRank_of_le hp.one_lt hle hMab hcard)
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle' : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨c, hBBs c.2⟩, rfl⟩
  have h2 : p ^ (r + 2) ≤ Nat.card (ggGamma K hBN).range * p := by
    rw [hcA, hS.1.2.1]
    exact Nat.pow_le_pow_right hp.pos hrank
  rw [pow_succ] at h2
  exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle'

theorem ggNbrInnerWeyl_of_ggTorusNoLineFieldComp (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I F : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsIF : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F))
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxI : ggLAut K θ ⟨x, hxK⟩ ∈ I)
    (hr : p ^ (r + 1) ≤ Nat.card (ggGamma K hN).range)
    (hT : GGTorusNoLineFieldComp p r R I F) :
    ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  classical
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma K hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ Subgroup.closure (I ∪ F),
      ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsIF b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  have h3 : p ^ 3 ≤ Nat.card γ.range := pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro n hn b hb
    obtain ⟨htp, htA⟩ := hW1 n hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hWA : ∀ n ∈ W, ∀ a ∈ γ.range, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ γ.range := by
    rintro n hn _ ⟨b, rfl⟩
    exact ⟨⟨(n : G) * b * (n : G)⁻¹, hWB n hn b b.2⟩,
      (ggGamma_conj K hN n b (hWB n hn b b.2)).symm ▸ rfl⟩
  have hxγ : γ ⟨x, hxBs⟩ ≠ 1 := by
    intro h1
    rw [hγ, ggGamma_eq_one_iff] at h1
    exact not_mem_centralizer_of_nbr hnb h1
  obtain ⟨n, hn, hmv⟩ := hW2 hWA (γ ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hxγ
    ⟨ggBeta K θ hN ⟨x, hxBs⟩, hxI, fun l => ggBeta_ggQuotHom K hN θ ⟨x, hxBs⟩ l⟩
    (ggFixCompCyclic_ggGamma_x hL hcfg
      (hPJ _ _ _ _ _ _ _ hcfg.1 hcfg.2.2) hnb hN hxBs)
  refine ⟨(n : G), n.2, fun b hb => ?_, fun hmem => hmv ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun c hc =>
      IsElemAbelian.comm hBs hc (hWB n hn b hb)
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have e : (⟨(n : G) * x * (n : G)⁻¹, hWB n hn x hxBs⟩ : Bs) = (⟨x, hxBs⟩ : Bs) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [← ggGamma_conj K hN n ⟨x, hxBs⟩ (hWB n hn x hxBs), e, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

end Config

theorem ggNbrInnerWeylOn_of_fieldLabelsComp (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p)) :
    GGNbrInnerWeylOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hxK P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hG G p B Bs x L D J hcfg y K hnb hN P hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hp2 hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ, hgr⟩, hQ⟩
    refine ⟨hs, hna, θ, hPθ, fun _ hxI => ?_⟩
    obtain ⟨hInn, r, hlift, hfix, hTc, hTf⟩ := hQ hs hna
    have hBsIF : ∀ (b : G) (hb : b ∈ Bs),
        ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F) := by
      intro b hb
      obtain ⟨u, hu, f, hf, e⟩ := hgr b hb
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hu))
        (Subgroup.closure_mono Set.subset_union_right hf)
    by_cases hall : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I
    · exact ggNbrInnerWeyl_of_ggTorusNoLineComp hL hPJ hcfg hnb hK θ hN hall
        (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hK θ hN hlift) hTc
    · push Not at hall
      exact ggNbrInnerWeyl_of_ggTorusNoLineFieldComp hL hPJ hcfg hnb hK θ hN hBsIF hxK hxI
        (pow_succ_le_card_range_ggGamma_of_field hcfg hnb hK θ hN hInn hfix hBsIF hall) hTf
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ, -⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

end CFSG.StandardType
