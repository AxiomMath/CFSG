module

import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3POdd
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G]

private theorem dvd_card_conj {L : Subgroup G} {g x : G} {q : ℕ}
    (h : q ∣ Nat.card ↥(L ⊓ centralizer ({g⁻¹ * x * g} : Set G))) :
    q ∣ Nat.card ↥(L.map (MulAut.conj g).toMonoidHom ⊓ centralizer ({x} : Set G)) := by
  rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _)] at h
  refine h.trans (card_dvd_of_le ?_)
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff] at hy
  refine mem_inf.2 ⟨mem_map_of_mem _ hy.1, mem_centralizer_singleton_iff.2 ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * x * g * y) * g⁻¹ := by rw [hy.2]
    _ = x * (g * y * g⁻¹) := by group

private theorem inducedBarInfAutHom_pow_eq_one {L : Subgroup G} {g : G}
    (hg : g ∈ normalizer (L : Set G)) {n : ℕ} (h : g ^ n = 1) :
    inducedBarInfAutHom L ⟨g, hg⟩ ^ n = 1 := by
  rw [← map_pow, show (⟨g, hg⟩ : ↥(normalizer (L : Set G))) ^ n = 1 from Subtype.ext h, map_one]

private theorem mem_normalizer_zpowers {X : Type*} [Group X] {β γ : X}
    (h : γ * β * γ⁻¹ = β ∨ γ * β * γ⁻¹ = β⁻¹) : γ ∈ normalizer (zpowers β : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers, MonoidHom.coe_coe, MulAut.conj_apply]
  rcases h with h | h <;> rw [h]
  exact zpowers_inv

variable [Finite G]

private theorem two_le_pRank_of_ne {M L L' C : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hZ : ¬ q ∣ Nat.card (center (Bar2 L))) (hCM : C ≤ M) (h : q ∣ Nat.card ↥(L ⊓ C))
    (h' : q ∣ Nat.card ↥(L' ⊓ C)) : 2 ≤ Open.pRank q C := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have h1 : ∀ X : Subgroup G, X ≤ M → q ∣ Nat.card X → 1 ≤ Open.pRank q (barImage M X) := by
    intro X hXM hX
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hX
    have hxo : orderOf (x : G) = q := by rw [Subgroup.orderOf_coe, hx]
    rw [show Open.pRank q (barImage M X) = Open.pRank q X from
      CFSG.AGLEmbedding.pRank_barM_eq hq hq2 M X hXM]
    exact UC6S846.le_pRank' hq (zpowers_le.2 x.2)
      (CFSG.Open.isElemAbelian_zpowers (by rw [← hxo]; exact pow_orderOf_eq_one _))
      (by rw [Nat.card_zpowers, hxo, pow_one])
  have hA := h1 _ (inf_le_left.trans hL.1.le) h
  have hB := h1 _ (inf_le_left.trans hL'.1.le) h'
  have hAL : barImage M (L ⊓ C) ≤ barImage M L := map_mono (comap_mono inf_le_left)
  have hBL : barImage M (L' ⊓ C) ≤ barImage M L' := map_mono (comap_mono inf_le_left)
  have hcomm := uc22p22l_barImage_commute hL hL' hne
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  have hle : barImage M (L ⊓ C) ⊓ barImage M (L' ⊓ C) ≤
      (center ↥(barImage M L)).map (barImage M L).subtype := fun z hz =>
    ⟨⟨z, hAL hz.1⟩, mem_center_iff.2 fun w => Subtype.ext (hcomm w w.2 z (hBL hz.2)), rfl⟩
  have hZ' := (Nat.card_congr (centerCongr e).toEquiv) ▸ hZ
  have hcop : Nat.Coprime q (Nat.card ↥(barImage M (L ⊓ C) ⊓ barImage M (L' ⊓ C))) :=
    (hq.coprime_iff_not_dvd).2 fun hd =>
      hZ' (card_map_of_injective (subtype_injective (barImage M L)) ▸ hd.trans (card_dvd_of_le hle))
  have hsum := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime hq
    (fun x hx y hy => hcomm x (hAL hx) y (hBL hy)) hcop
  have hmono := CFSG.SectionRank.pRank_mono hq.one_lt
    (sup_le (map_mono (comap_mono inf_le_right)) (map_mono (comap_mono inf_le_right)) :
      barImage M (L ⊓ C) ⊔ barImage M (L' ⊓ C) ≤ barImage M C)
  have hC : Open.pRank q (barImage M C) = Open.pRank q C :=
    CFSG.AGLEmbedding.pRank_barM_eq hq hq2 M C hCM
  omega

theorem uc22s2112l3p_false_of_ne {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {p : ℕ} [Fact p.Prime] (hp11 : 11 ≤ p) (hZ : ¬ p ∣ Nat.card (center (Bar2 L)))
    (hpL : 2 ≤ Open.pRank p L) {b : G} (hbB : b ∈ c.B0) (hbp : (orderOf b).Prime)
    {D0 : Subgroup G} (hD0 : D0 ≤ L ⊓ centralizer ({b} : Set G)) (hD0perf : ⁅D0, D0⁆ = D0)
    (f0 : ↥D0 →* PSL(2, GaloisField p 1)) (hf0 : Function.Surjective f0) {g : G} (hg : g ∈ D.M)
    (hne : L.map (MulAut.conj g).toMonoidHom ≠ L)
    (hpg : p ∣ Nat.card ↥(L.map (MulAut.conj g).toMonoidHom ⊓ centralizer ({b} : Set G))) :
    False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hS, hSns, -, hpS⟩ := uc22s2112r2_psl2_facts (p := p) hp2 le_rfl (by rw [pow_one]; omega)
  rw [pow_one] at hpS
  obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hpL
  have h4 := UC6S846.calCRankTwice D.M L hL
    (fun h => hne (UC6S846.mem_normalizer_iff_map_conj.1 (h hg))) p hp hp2 hZ E hEL hEel 2 hEc
  have hpσ := hσ.four_mem p hp hp2 (by omega)
  have hMs := UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  have hL' : L.map (MulAut.conj g).toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M _
    (UC6S846.mem_normalizer_iff_map_conj.1 (le_normalizer hg)) hL
  obtain ⟨hHne, hHM, -, hCH⟩ := uc22s2112r2_normalizer hH c hL.1.le hbB hbp
  obtain ⟨-, -, -, hCH'⟩ := uc22s2112r2_normalizer hH c hL'.1.le hbB hbp
  have hpL0 : p ∣ Nat.card ↥(L ⊓ centralizer ({b} : Set G)) :=
    hpS.trans ((Subgroup.card_dvd_of_surjective hf0).trans (card_dvd_of_le hD0))
  have hrank := two_le_pRank_of_ne hp hp2 hL hL' hne.symm hZ inf_le_right
    (hpL0.trans (card_dvd_of_le (le_inf inf_le_left hCH)))
    (hpg.trans (card_dvd_of_le (le_inf inf_le_left hCH')))
  exact uc22s2112r2_false_of_kf7 hKF7 hpσ hMs hHne hHM hrank (hD0.trans hCH) hD0perf hSns f0 hf0
    hpS fun h => by omega

theorem uc22s2112l3p_normalizes {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (h5 : S21_5 D Ch) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hpL : 2 ≤ Open.pRank p L) {b : G} (hbB : b ∈ c.B0)
    (hb : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (D.T : Set G))
    (hbp : (orderOf b).Prime) (hb5 : 5 ≤ orderOf b)
    (hbN : ¬ orderOf b ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hcomm : ∀ τ : G, ∀ hτ : τ ∈ normalizer (L : Set G), τ ∈ D.T →
      inducedBarInfAutHom L ⟨b, hb⟩ * inducedBarInfAutHom L ⟨τ, hτ⟩ =
        inducedBarInfAutHom L ⟨τ, hτ⟩ * inducedBarInfAutHom L ⟨b, hb⟩)
    {Y : Subgroup (BarInf L)} (hY : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩))
    (eY : ↥Y ≃* SL(2, ZMod p)) {t : G} (htM : t ∈ D.M) (ht : t * b * t⁻¹ = b⁻¹) :
    D.T ≤ normalizer (L : Set G) ∧ t ∈ normalizer (L : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by omega
  obtain ⟨hdvd, D0, hD0, hD0perf, f0, hf0⟩ := uc22s2112l3p_lift hb hbp hbN hp5 hY eY
  have key : ∀ g ∈ D.M, p ∣ Nat.card ↥(L ⊓ centralizer ({g⁻¹ * b * g} : Set G)) →
      g ∈ normalizer (L : Set G) := fun g hg hpg => by
    by_contra hgN
    exact uc22s2112l3p_false_of_ne hσ hKF7 hH c hL hp11 hZ hpL hbB hbp hD0 hD0perf f0 hf0 hg
      (fun h => hgN (UC6S846.mem_normalizer_iff_map_conj.2 h)) (dvd_card_conj hpg)
  refine ⟨fun τ hτT => key τ (D.sylowM.le hτT) ?_, key t htM ?_⟩
  ·
    have hbτ : b ∈ normalizer ((L.map (MulAut.conj τ).toMonoidHom : Subgroup G) : Set G) :=
      h5 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } _ (UC6S846.calC_map D.M _
        (UC6S846.mem_normalizer_iff_map_conj.1 (le_normalizer (D.sylowM.le hτT))) hL) hbB
    have hb' : τ⁻¹ * b * τ ∈ normalizer (L : Set G) := by
      rw [mem_normalizer_iff]
      intro l
      have h1 := mem_normalizer_iff.1 hbτ (τ * l * τ⁻¹)
      simp only [mem_map_equiv, MulAut.conj_symm_apply] at h1
      rwa [show τ⁻¹ * (τ * l * τ⁻¹) * τ = l by group,
        show τ⁻¹ * (b * (τ * l * τ⁻¹) * b⁻¹) * τ = τ⁻¹ * b * τ * l * (τ⁻¹ * b * τ)⁻¹ by group]
        at h1
    have hob : orderOf (τ⁻¹ * b * τ) = orderOf b := by
      rw [← MulAut.conj_symm_apply, MulEquiv.orderOf_eq]
    have huT : b⁻¹ * (τ⁻¹ * b * τ) ∈ D.T := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hbT) τ⁻¹).1 (inv_mem hτT)
      rw [inv_inv] at h1
      simpa only [mul_assoc] using mul_mem h1 hτT
    have huN : b⁻¹ * (τ⁻¹ * b * τ) ∈ normalizer (L : Set G) := mul_mem (inv_mem hb) hb'
    have hθ' : inducedBarInfAutHom L ⟨_, hb'⟩ =
        inducedBarInfAutHom L ⟨b, hb⟩ * inducedBarInfAutHom L ⟨_, huN⟩ := by
      rw [← map_mul]
      exact congrArg _ (Subtype.ext (mul_inv_cancel_left b _).symm)
    have hu1 : inducedBarInfAutHom L ⟨_, huN⟩ = 1 := by
      have hc : Commute (inducedBarInfAutHom L ⟨b, hb⟩) (inducedBarInfAutHom L ⟨_, huN⟩) :=
        hcomm _ huN huT
      have hs := inducedBarInfAutHom_pow_eq_one hb' (n := orderOf b)
        (by rw [← hob]; exact pow_orderOf_eq_one _)
      rw [hθ', hc.mul_pow, inducedBarInfAutHom_pow_eq_one hb (pow_orderOf_eq_one b), one_mul] at hs
      obtain ⟨k, hk⟩ := D.sylowG.isPGroup ⟨_, huT⟩
      have h2 := inducedBarInfAutHom_pow_eq_one huN (n := 2 ^ k) (congrArg Subtype.val hk)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_right k ((Nat.coprime_primes hbp Nat.prime_two).2 (by omega)))
        (orderOf_dvd_of_pow_eq_one hs) (orderOf_dvd_of_pow_eq_one h2))
    have hY' : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨_, hb'⟩) := by
      rwa [hθ', hu1, mul_one]
    exact (uc22s2112l3p_lift hb' (hob ▸ hbp) (hob ▸ hbN) hp5 hY' eY).1 p (dvd_mul_right p _)
  ·
    have htb : t⁻¹ * b * t = b⁻¹ := by
      calc t⁻¹ * b * t = t⁻¹ * (b⁻¹)⁻¹ * t := by rw [inv_inv]
        _ = t⁻¹ * (t * b * t⁻¹)⁻¹ * t := by rw [ht]
        _ = b⁻¹ := by group
    have hC : centralizer ({b⁻¹} : Set G) = centralizer ({b} : Set G) := by
      ext y
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      exact Commute.inv_right_iff
    rw [htb, hC]
    exact hdvd p (dvd_mul_right p _)

theorem uc22s2112l3p_false_of_inv {D : Data G} {L : Subgroup G} {b : G}
    (hb : b ∈ normalizer (L : Set G)) (hbp : (orderOf b).Prime) (hb5 : 5 ≤ orderOf b)
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1) (hTN : D.T ≤ normalizer (L : Set G))
    (hcomm : ∀ τ : G, ∀ hτ : τ ∈ normalizer (L : Set G), τ ∈ D.T →
      inducedBarInfAutHom L ⟨b, hb⟩ * inducedBarInfAutHom L ⟨τ, hτ⟩ =
        inducedBarInfAutHom L ⟨τ, hτ⟩ * inducedBarInfAutHom L ⟨b, hb⟩)
    {t : G} (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (htN : t ∈ normalizer (L : Set G))
    (ht : t * b * t⁻¹ = b⁻¹) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := inducedBarInfAutHom L
  set β := θ ⟨b, hb⟩
  let H : Subgroup G :=
    ((normalizer ((zpowers β : Subgroup _) : Set (MulAut (BarInf L)))).comap θ).map
      (normalizer (L : Set G)).subtype
  have hmem : ∀ (g : G) (hg : g ∈ normalizer (L : Set G)),
      (θ ⟨g, hg⟩ * β * (θ ⟨g, hg⟩)⁻¹ = β ∨ θ ⟨g, hg⟩ * β * (θ ⟨g, hg⟩)⁻¹ = β⁻¹) → g ∈ H :=
    fun g hg h => ⟨⟨g, hg⟩, mem_normalizer_zpowers h, rfl⟩
  have hTH : D.T ≤ H := fun τ hτ =>
    hmem τ (hTN hτ) (Or.inl (by rw [← hcomm τ (hTN hτ) hτ, mul_inv_cancel_right]))
  have hθt : θ ⟨t, htN⟩ * β * (θ ⟨t, htN⟩)⁻¹ = β⁻¹ := by
    have := congrArg θ (show (⟨t, htN⟩ : ↥(normalizer (L : Set G))) * ⟨b, hb⟩ * (⟨t, htN⟩)⁻¹ =
      (⟨b, hb⟩)⁻¹ from Subtype.ext ht)
    simpa only [map_mul, map_inv] using this
  have htH : t ∈ H := hmem t htN (Or.inr hθt)
  obtain ⟨Q, hQ⟩ := (D.sylowG.of_le hTH le_top).exists_sylow_eq_subgroupOf
  obtain ⟨k, hk⟩ := ht2
  have h2t : IsPGroup 2 (zpowers (⟨t, htH⟩ : ↥H)) := IsPGroup.of_card_dvd_pow (n := k)
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one (Subtype.ext hk))
  obtain ⟨Q', hQ'⟩ := h2t.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq ↥H Q Q'
  have hu : h⁻¹ * ⟨t, htH⟩ * h ∈ (Q : Subgroup ↥H) := by
    simpa [mul_assoc] using (mem_pointwise_smul_iff_inv_smul_mem).1 (hQ' (mem_zpowers _))
  rw [hQ, mem_subgroupOf] at hu
  obtain ⟨n, hnβ, hnh⟩ := h.2
  have hn : (n : G) = h := hnh
  have huT : ((n⁻¹ * ⟨t, htN⟩ * n : ↥(normalizer (L : Set G))) : G) ∈ D.T := by
    simpa [hn] using hu
  have hc : β * θ (n⁻¹ * ⟨t, htN⟩ * n) = θ (n⁻¹ * ⟨t, htN⟩ * n) * β := hcomm _ _ huT
  rw [map_mul, map_mul, map_inv] at hc
  have hnβ' : θ n ∈ normalizer ((zpowers β : Subgroup _) : Set (MulAut (BarInf L))) := hnβ
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 ((mem_normalizer_iff.1 (inv_mem hnβ') β).1 (mem_zpowers β))
  have hcj := ((show Commute β _ from hc).zpow_left j).eq
  rw [hj] at hcj
  have hct : β * θ ⟨t, htN⟩ = θ ⟨t, htN⟩ * β := by
    have h3 : (θ n)⁻¹ * (β * θ ⟨t, htN⟩) * θ n = (θ n)⁻¹ * (θ ⟨t, htN⟩ * β) * θ n := by
      calc (θ n)⁻¹ * (β * θ ⟨t, htN⟩) * θ n
          = (θ n)⁻¹ * β * (θ n)⁻¹⁻¹ * ((θ n)⁻¹ * θ ⟨t, htN⟩ * θ n) := by group
        _ = (θ n)⁻¹ * θ ⟨t, htN⟩ * θ n * ((θ n)⁻¹ * β * (θ n)⁻¹⁻¹) := hcj
        _ = (θ n)⁻¹ * (θ ⟨t, htN⟩ * β) * θ n := by group
    exact mul_left_cancel (mul_right_cancel h3)
  have h4 : β⁻¹ = β := by rw [← hθt, ← hct, mul_inv_cancel_right]
  have hβ2 : β ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [← h4]; exact inv_mul_cancel β
  have hβs : β ^ orderOf b = 1 := inducedBarInfAutHom_pow_eq_one hb (pow_orderOf_eq_one b)
  exact hθ (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_primes Nat.prime_two hbp).2 (by omega)) (orderOf_dvd_of_pow_eq_one hβ2)
    (orderOf_dvd_of_pow_eq_one hβs)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
