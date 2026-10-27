module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.GLTheoremB (quotAutHom quotAutHom_mk)

section Main

theorem uc22p22r_exists_rbar {Mb : Type} [Group Mb] [Finite Mb] {Vmod : Type} [AddCommGroup Vmod]
    [Module (ZMod 2) Vmod] [Finite Vmod] (ρ : Representation (ZMod 2) Mb Vmod) {Kb Tb : Subgroup Mb} {t : Mb}
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (hKb : IsL2 ↥Kb n)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 Tb ⊤) (htT : t ∈ Tb) (htK : t ∉ normalizer (Kb : Set Mb))
    (hcomm : ∀ a ∈ Kb, ∀ b ∈ Kb.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hXn : (Kb ⊔ Kb.map (MulAut.conj t).toMonoidHom).Normal)
    (hne : Kb ⊔ Kb.map (MulAut.conj t).toMonoidHom ≠ CFSG.RankThree.PartOne.pElementSubgroup p ⊤)
    (hF1 : ∀ c ∈ centralizer ((Kb ⊔ Kb.map (MulAut.conj t).toMonoidHom : Subgroup Mb) : Set Mb),
      (∃ k : ℕ, c ^ (p ^ k) = 1) → c = 1)
    {Y : Submodule (ZMod 2) Vmod} (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (normalizer (Kb : Set Mb)) Y)
    (hF2 : ∀ S : Subgroup Mb, CFSG.ABGLocalTools.IsSylowOf 2 S
      ((Kb ⊔ Kb.map (MulAut.conj t).toMonoidHom) ⊔
        centralizer ((Kb ⊔ Kb.map (MulAut.conj t).toMonoidHom : Subgroup Mb) : Set Mb)) →
      ¬ Nat.card ↥(fixOn ρ S Y) ≡ 1 [MOD p]) :
    ∃ (R : Subgroup Mb) (z : Mb), Tb ≤ normalizer (R : Set Mb) ∧ ((R ⊓ Tb).subgroupOf R).Normal ∧ z ∈ R ∧
      orderOf z = p ∧ R = (R ⊓ Tb) ⊔ Subgroup.zpowers z ∧ ∃ w : Vmod, w ≠ 0 ∧ ∀ r ∈ R ⊔ Tb, ρ r w = w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kt := Kb.map (MulAut.conj t).toMonoidHom with hKt
  set X := Kb ⊔ Kt with hX
  set C := centralizer (X : Set Mb) with hC
  have hKtL2 : IsL2 ↥Kt n :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Kb.equivMapOfInjective _ (MulAut.conj t).injective) hKb
  have hZK := uc22p22g_center_bot hKb
  have hZKt := uc22p22g_center_bot hKtL2
  have hKs : IsSimpleGroup ↥Kb := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hKb
  have hKts : IsSimpleGroup ↥Kt := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hKtL2
  have hcardKt : Nat.card Kt = Nat.card Kb := Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hXZ : X ⊓ C = ⊥ := uc22p22r_inf_centralizer_eq_bot hcomm hZK hZKt
  have hconj := uc22p22r_conj_eq_or hKs hcomm hZK hcardKt hXn
  have hNn : (normalizer (Kb : Set Mb)).Normal := uc22p22r_normalizer_normal hconj
  have hNKt : normalizer (Kb : Set Mb) ≤ normalizer (Kt : Set Mb) := by
    intro h hh
    have hht : h * t ∉ normalizer (Kb : Set Mb) := fun h' => htK (by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) h'
      rwa [inv_mul_cancel_left] at this)
    have h1 : Kb.map (MulAut.conj (h * t)).toMonoidHom = Kt :=
      (hconj (h * t)).resolve_left fun h' => hht (Subgroup.mem_normalizer_iff_map_conj_eq.2 h')
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show Kt.map (MulAut.conj h).toMonoidHom = Kt
    rw [hKt, ← uc22p22r_map_conj_mul]
    exact h1
  have htt : t * t ∈ normalizer (Kb : Set Mb) := by
    have := uc22p22r_inv_mul_mem_normalizer hconj (g := t⁻¹) (h := t)
      (fun h' => htK (by simpa using Subgroup.inv_mem _ h')) htK
    rwa [inv_inv] at this
  have hCK : C ≤ normalizer (Kb : Set Mb) := by
    intro c hc
    apply Subgroup.mem_normalizer_fintype
    intro k hk
    have h1 : k * c = c * k := Subgroup.mem_centralizer_iff.1 hc k (le_sup_left (b := Kt) hk)
    rw [← h1, mul_inv_cancel_right]
    exact hk
  set XC := X ⊔ C with hXC
  haveI hXCn : XC.Normal := Subgroup.sup_normal X C
  have hXCle : XC ≤ normalizer (Kb : Set Mb) := sup_le (uc22p22r_sup_le_normalizer_left hcomm) hCK
  have hXle : X ≤ CFSG.RankThree.PartOne.pElementSubgroup p ⊤ := by
    obtain ⟨z₁, hz₁⟩ := uc22p22r_L2_exists_orderOf hKb hp hpn
    obtain ⟨z₂, hz₂⟩ := uc22p22r_L2_exists_orderOf hKtL2 hp hpn
    refine sup_le (uc22p22r_le_pElementSubgroup hKs z₁.2 (by rw [Subgroup.orderOf_coe, hz₁]) ?_)
      (uc22p22r_le_pElementSubgroup hKts z₂.2 (by rw [Subgroup.orderOf_coe, hz₂]) ?_)
    · intro h
      have h' : z₁ = 1 := Subtype.ext h
      rw [h', orderOf_one] at hz₁
      exact hp.ne_one hz₁.symm
    · intro h
      have h' : z₂ = 1 := Subtype.ext h
      rw [h', orderOf_one] at hz₂
      exact hp.ne_one hz₂.symm
  obtain ⟨y, hyX, ky, hky⟩ := uc22p22r_exists_pElt_not_mem hXle hne
  have hyXC : y ∉ XC := fun h =>
    hyX (uc22p22r_mem_of_pElt hXZ hF1 h (k := ky) (by rw [← hky, pow_orderOf_eq_one]))
  set S' := Tb ⊓ XC with hS'
  have hS'syl : CFSG.ABGLocalTools.IsSylowOf 2 S' XC :=
    hT.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.2 hXCn])
  set NS := normalizer (S' : Set Mb) with hNS
  have hFrat : NS ⊔ XC = ⊤ := by
    obtain ⟨Q, hQ⟩ := hS'syl
    have := Sylow.normalizer_sup_eq_top Q
    rwa [hQ] at this
  have hXCNS : NS ≤ normalizer (XC : Set Mb) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hXCn]
    exact le_top
  have hsurj : ∀ g : Mb, ∃ m ∈ NS, ∃ x ∈ XC, m * x = g := by
    intro g
    have hg : g ∈ NS ⊔ XC := hFrat ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right NS XC hXCNS, Set.mem_mul] at hg
    exact hg
  set π₀ : Mb →* Mb ⧸ XC := QuotientGroup.mk' XC with hπ₀
  have hπ₀1 : ∀ g, π₀ g = 1 ↔ g ∈ XC := fun g => QuotientGroup.eq_one_iff g
  have hy₀ : π₀ y ≠ 1 := fun h => hyXC ((hπ₀1 y).1 h)
  have hy₀p : π₀ y ^ (p ^ ky) = 1 := by rw [← map_pow, ← hky, pow_orderOf_eq_one, map_one]
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hy₀p)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hjo
    exact hy₀ hjo
  have hy₁1 : π₀ (y ^ (p ^ (j - 1))) ≠ 1 := by
    intro h
    rw [map_pow] at h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hjo] at h1
    have h2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1
    omega
  have hy₁p : π₀ (y ^ (p ^ (j - 1))) ^ p = 1 := by
    rw [map_pow, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hjo,
      pow_orderOf_eq_one]
  obtain ⟨a₀, ha₀NS, x₀, hx₀, ha₀x⟩ := hsurj (y ^ (p ^ (j - 1)))
  have hπa₀ : π₀ a₀ = π₀ (y ^ (p ^ (j - 1))) := by rw [← ha₀x, map_mul, (hπ₀1 x₀).2 hx₀, mul_one]
  have ha₀XC : a₀ ∉ XC := fun h => hy₁1 (by rw [← hπa₀]; exact (hπ₀1 a₀).2 h)
  have ha₀p : a₀ ^ p ∈ XC := (hπ₀1 _).1 (by rw [map_pow, hπa₀, hy₁p])
  have ha₀K : a₀ ∈ normalizer (Kb : Set Mb) := by
    by_contra h
    have h2 : a₀ * a₀ ∈ normalizer (Kb : Set Mb) := by
      have := uc22p22r_inv_mul_mem_normalizer hconj (g := a₀⁻¹) (h := a₀)
        (fun h' => h (by simpa using Subgroup.inv_mem _ h')) h
      rwa [inv_inv] at this
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have e : a₀ = ((a₀ * a₀) ^ m)⁻¹ * a₀ ^ p := by
      rw [hm, pow_succ, pow_mul, sq, inv_mul_cancel_left]
    apply h
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ h2 m)) (hXCle ha₀p)
  set N₁ := NS ⊓ normalizer (Kb : Set Mb) with hN₁
  set N₂ := NS ⊓ XC with hN₂
  have hN₂N₁ : N₂ ≤ N₁ := inf_le_inf_left _ hXCle
  have ha₀N₁ : a₀ ∈ N₁ := ⟨ha₀NS, ha₀K⟩
  have hTS' : Tb ≤ NS := by
    intro s hs
    apply Subgroup.mem_normalizer_fintype
    rintro x ⟨hxT, hxXC⟩
    exact ⟨Tb.mul_mem (Tb.mul_mem hs hxT) (Tb.inv_mem hs), hXCn.conj_mem x hxXC s⟩
  have hTN₁ : Tb ≤ normalizer (N₁ : Set Mb) := by
    intro s hs
    apply Subgroup.mem_normalizer_fintype
    rintro x ⟨hxNS, hxK⟩
    exact ⟨NS.mul_mem (NS.mul_mem (hTS' hs) hxNS) (NS.inv_mem (hTS' hs)), hNn.conj_mem x hxK s⟩
  have hN₁N₂ : N₁ ≤ normalizer (N₂ : Set Mb) := by
    intro g hg
    apply Subgroup.mem_normalizer_fintype
    rintro x ⟨hxNS, hxXC⟩
    exact ⟨NS.mul_mem (NS.mul_mem hg.1 hxNS) (NS.inv_mem hg.1), hXCn.conj_mem x hxXC g⟩
  have hTN₂ : Tb ≤ normalizer (N₂ : Set Mb) := by
    intro s hs
    apply Subgroup.mem_normalizer_fintype
    rintro x ⟨hxNS, hxXC⟩
    exact ⟨NS.mul_mem (NS.mul_mem (hTS' hs) hxNS) (NS.inv_mem (hTS' hs)), hXCn.conj_mem x hxXC s⟩
  have hcommN₁ : ∀ g ∈ N₁, ∀ h ∈ N₁, g * h * g⁻¹ * h⁻¹ ∈ N₂ := by
    intro g hg h hh
    refine ⟨NS.mul_mem (NS.mul_mem (NS.mul_mem hg.1 hh.1) (NS.inv_mem hg.1)) (NS.inv_mem hh.1), ?_⟩
    obtain ⟨k, hk, hkx⟩ := uc22p22r_comm_inner hKb hg.2 hh.2
    obtain ⟨l, hl, hlx⟩ := uc22p22r_comm_inner hKtL2 (hNKt hg.2) (hNKt hh.2)
    exact uc22p22r_mem_of_inner hcomm hk hl hkx hlx
  haveI hQn : (N₂.subgroupOf N₁).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN₂N₁).2 hN₁N₂
  set q : ↥N₁ →* ↥N₁ ⧸ N₂.subgroupOf N₁ := QuotientGroup.mk' (N₂.subgroupOf N₁) with hq
  have hq1 : ∀ x : ↥N₁, q x = 1 ↔ (x : Mb) ∈ N₂ := fun x => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQc : ∀ x y : ↥N₁ ⧸ N₂.subgroupOf N₁, x * y = y * x := by
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N₂.subgroupOf N₁) x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N₂.subgroupOf N₁) y
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h1 := hcommN₁ _ (N₁.inv_mem y.2) _ (N₁.inv_mem x.2)
    have e : (((x * y : ↥N₁)⁻¹ * (y * x) : ↥N₁) : Mb) =
        (y : Mb)⁻¹ * (x : Mb)⁻¹ * ((y : Mb)⁻¹)⁻¹ * ((x : Mb)⁻¹)⁻¹ := by
      simp [mul_assoc]
    rw [e]
    exact h1
  let ρ₁ : ↥Tb →* MulAut ↥N₁ := N₁.normalizerMonoidHom.comp (Subgroup.inclusion hTN₁)
  have hρ₁ : ∀ (s : ↥Tb) (x : ↥N₁), ((ρ₁ s x : ↥N₁) : Mb) = (s : Mb) * x * (s : Mb)⁻¹ := by
    intro s x
    simp [ρ₁]
  have hρ₁N : ∀ s : ↥Tb, (N₂.subgroupOf N₁).map (ρ₁ s).toMonoidHom = N₂.subgroupOf N₁ := by
    intro s
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : Mb) ∈ N₂ := hy
      show ((ρ₁ s y : ↥N₁) : Mb) ∈ N₂
      rw [hρ₁]
      exact (Subgroup.mem_normalizer_iff.1 (hTN₂ s.2) _).1 hy'
    · intro hx
      have hx' : (x : Mb) ∈ N₂ := hx
      refine ⟨(ρ₁ s)⁻¹ x, ?_, by simp⟩
      show (((ρ₁ s)⁻¹ x : ↥N₁) : Mb) ∈ N₂
      have h1 : ((ρ₁ s⁻¹ x : ↥N₁) : Mb) = (s : Mb)⁻¹ * x * (s : Mb) := by
        rw [hρ₁]
        simp
      have h2 : (ρ₁ s)⁻¹ x = ρ₁ s⁻¹ x := by rw [map_inv]
      rw [h2, h1]
      have := (Subgroup.mem_normalizer_iff.1 (hTN₂ (Tb.inv_mem s.2)) _).1 hx'
      simpa using this
  let θ : ↥Tb →* MulAut (↥N₁ ⧸ N₂.subgroupOf N₁) := quotAutHom (N₂.subgroupOf N₁) ρ₁ hρ₁N
  have hθ : ∀ (s : ↥Tb) (x : ↥N₁), θ s (q x) = q (ρ₁ s x) := fun s x => quotAutHom_mk _ _ _ s x
  have hθ1 : ∀ s : ↥Tb, (s : Mb) ∈ normalizer (Kb : Set Mb) → ∀ x, θ s x = x := by
    intro s hs x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N₂.subgroupOf N₁) x
    have hsN₁ : (s : Mb) ∈ N₁ := ⟨hTS' s.2, hs⟩
    have h1 : ρ₁ s x = ⟨s, hsN₁⟩ * x * ⟨s, hsN₁⟩⁻¹ := Subtype.ext (by rw [hρ₁]; rfl)
    show θ s (q x) = q x
    rw [hθ, h1, map_mul, map_mul, map_inv, hQc (q ⟨s, hsN₁⟩) (q x), mul_assoc, mul_inv_cancel, mul_one]
  set τ := θ ⟨t, htT⟩ with hτdef
  have hτ : ∀ x, τ (τ x) = x := by
    intro x
    have h1 : τ (τ x) = θ (⟨t, htT⟩ * ⟨t, htT⟩) x := by
      rw [map_mul, MulAut.mul_apply]
    rw [h1]
    exact hθ1 _ htt x
  have hθt : ∀ s : ↥Tb, (s : Mb) ∉ normalizer (Kb : Set Mb) → ∀ x, θ s x = τ x := by
    intro s hs x
    have h1 : t⁻¹ * s ∈ normalizer (Kb : Set Mb) := uc22p22r_inv_mul_mem_normalizer hconj htK hs
    have h1' : (((⟨t, htT⟩⁻¹ * s : ↥Tb)) : Mb) ∈ normalizer (Kb : Set Mb) := by simpa using h1
    have h2 : s = ⟨t, htT⟩ * (⟨t, htT⟩⁻¹ * s) := by group
    rw [h2, map_mul, MulAut.mul_apply, hθ1 _ h1']
  have ha₀o : orderOf (q ⟨a₀, ha₀N₁⟩) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hq1]
      exact ⟨NS.pow_mem ha₀NS p, ha₀p⟩
    · rw [Ne, hq1]
      exact fun h => ha₀XC h.2
  obtain ⟨b, hbo, hbτ⟩ := uc22p22r_eigen hQc hp τ hτ ha₀o
  have hbinv : ∀ s : ↥Tb, ∀ x ∈ Subgroup.zpowers b, θ s x ∈ Subgroup.zpowers b := by
    have hθb : ∀ s : ↥Tb, θ s b ∈ Subgroup.zpowers b := by
      intro s
      by_cases hs : (s : Mb) ∈ normalizer (Kb : Set Mb)
      · rw [hθ1 s hs]
        exact Subgroup.mem_zpowers b
      · rw [hθt s hs]
        rcases hbτ with h | h
        · rw [h]
          exact Subgroup.mem_zpowers b
        · rw [h]
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b)
    intro s x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (hθb s) i
  set N₃ := ((Subgroup.zpowers b).comap q).map N₁.subtype with hN₃
  have hN₃N₁ : N₃ ≤ N₁ := Subgroup.map_subtype_le _
  have hN₂N₃ : N₂ ≤ N₃ := by
    intro x hx
    refine ⟨⟨x, hN₂N₁ hx⟩, ?_, rfl⟩
    show q ⟨x, hN₂N₁ hx⟩ ∈ Subgroup.zpowers b
    rw [(hq1 _).2 hx]
    exact Subgroup.one_mem _
  have hTN₃ : Tb ≤ normalizer (N₃ : Set Mb) := by
    intro s hs
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨ρ₁ ⟨s, hs⟩ x, ?_, hρ₁ ⟨s, hs⟩ x⟩
    show q (ρ₁ ⟨s, hs⟩ x) ∈ Subgroup.zpowers b
    rw [← hθ]
    exact hbinv ⟨s, hs⟩ _ hx
  have hN₃card : Nat.card N₃ = Nat.card N₂ * p := by
    rw [hN₃, Subgroup.card_map_of_injective N₁.subtype_injective, hq, uc22p22r_card_comap_mk,
      Nat.card_zpowers, hbo, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₂N₁).toEquiv]
  have hpN₂ : ¬ p ∣ Nat.card N₂ := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₂) p hdvd
    have hx1 : (x : Mb) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
    have hxX : (x : Mb) ∈ X := uc22p22r_mem_of_pElt hXZ hF1 x.2.2 (k := 1) (by rw [pow_one]; exact hx1)
    have hSK : CFSG.ABGLocalTools.IsSylowOf 2 (S' ⊓ Kb) Kb :=
      hS'syl.inf_of_le_normalizer (le_sup_left.trans le_sup_left) hXCle
    have hSKt : CFSG.ABGLocalTools.IsSylowOf 2 (S' ⊓ Kt) Kt :=
      hS'syl.inf_of_le_normalizer (le_sup_right.trans le_sup_left) (hXCle.trans hNKt)
    have h1 := uc22p22r_eq_one_of_pElt_normalizer hcomm hKb hKtL2 hp hp2 hpn hSK hSKt hxX x.2.1 hx1
    have h2 : x = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hS'N₂ : S' ≤ N₂ := le_inf Subgroup.le_normalizer inf_le_right
  have hS'N₃ : S' ≤ N₃ := hS'N₂.trans hN₂N₃
  have hS'syl₂ : CFSG.ABGLocalTools.IsSylowOf 2 S' N₂ := hS'syl.of_le hS'N₂ inf_le_right
  have hm₂ := (CFSG.ABGLocalTools.isSylowOf_iff.1 hS'syl₂).2.2
  have hN₂rel : S'.relIndex N₂ * Nat.card S' = Nat.card N₂ := by
    have := Subgroup.relIndex_mul_card (H := S') (K := N₂)
    rwa [inf_of_le_left hS'N₂] at this
  have hN₃rel : S'.relIndex N₃ * Nat.card S' = Nat.card N₃ := by
    have := Subgroup.relIndex_mul_card (H := S') (K := N₃)
    rwa [inf_of_le_left hS'N₃] at this
  have hS'pos : 0 < Nat.card S' := Nat.card_pos
  have hrel : S'.relIndex N₃ = S'.relIndex N₂ * p := by
    apply Nat.eq_of_mul_eq_mul_right hS'pos
    rw [hN₃rel, hN₃card, ← hN₂rel]
    ring
  haveI hS'n : (S'.subgroupOf N₃).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS'N₃).2 (hN₃N₁.trans inf_le_left)
  have hcardQ : Nat.card (↥N₃ ⧸ S'.subgroupOf N₃) = S'.relIndex N₂ * p := by
    rw [← hrel, Subgroup.relIndex, Subgroup.index_eq_card]
  have hodd : ¬ 2 ∣ Nat.card (↥N₃ ⧸ S'.subgroupOf N₃) := by
    rw [hcardQ]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h' | h'
    · exact hm₂ h'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h').symm
  have hfac : (Nat.card (↥N₃ ⧸ S'.subgroupOf N₃)).factorization p = 1 := by
    have hm0 : S'.relIndex N₂ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hN₂rel
      exact (Nat.card_pos (α := ↥N₂)).ne' hN₂rel.symm
    have hpm : ¬ p ∣ S'.relIndex N₂ := fun h => hpN₂ (hN₂rel ▸ h.mul_right _)
    rw [hcardQ, Nat.factorization_mul hm0 hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpm, hp.factorization_self, zero_add]
  have hT2 : IsPGroup 2 Tb := hT.isPGroup
  have hTS'' : Tb ≤ normalizer (S' : Set Mb) := hTS'
  obtain ⟨R, hS'R, hRN₃, hTR, hRcard⟩ :=
    uc22p22r_exists_invariant_lift hT2 hS'N₃ hTN₃ hTS'' hodd hp
  rw [hfac, pow_one] at hRcard
  have hRN₁ : R ≤ N₁ := hRN₃.trans hN₃N₁
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) p (by rw [hRcard]; exact dvd_mul_left p _)
  set z : Mb := (z' : Mb) with hzdef
  have hzR : z ∈ R := z'.2
  have hzo : orderOf z = p := by rw [hzdef, Subgroup.orderOf_coe, hz']
  obtain ⟨kS, hkS⟩ := (hT2.to_le (inf_le_left : S' ≤ Tb)).exists_card_eq
  have hcopS : Nat.Coprime (Nat.card S') p := by
    rw [hkS]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hRT : R ⊓ Tb = S' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (le_inf hS'R inf_le_left) ?_
    obtain ⟨i, hi⟩ := (hT2.to_le (inf_le_right : R ⊓ Tb ≤ Tb)).exists_card_eq
    have hdvd : Nat.card ↥(R ⊓ Tb) ∣ Nat.card S' * p := hRcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hcop : Nat.Coprime (2 ^ i) p :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    rw [hi] at hdvd ⊢
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)
  have hRz : R = (R ⊓ Tb) ⊔ Subgroup.zpowers z := by
    rw [hRT]
    symm
    refine Subgroup.eq_of_le_of_card_ge (sup_le hS'R (Subgroup.zpowers_le.2 hzR)) ?_
    rw [hRcard]
    apply Nat.le_of_dvd Nat.card_pos
    have h1 : Nat.card S' ∣ Nat.card ↥(S' ⊔ Subgroup.zpowers z) := Subgroup.card_dvd_of_le le_sup_left
    have h2 : p ∣ Nat.card ↥(S' ⊔ Subgroup.zpowers z) := by
      have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers z ≤ S' ⊔ Subgroup.zpowers z)
      rwa [Nat.card_zpowers, hzo] at this
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopS h1 h2
  have hRn : ((R ⊓ Tb).subgroupOf R).Normal := by
    rw [hRT]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hS'R).2 (hRN₁.trans inf_le_left)
  refine ⟨R, z, hTR, hRn, hzR, hzo, hRz, ?_⟩
  have hzN : Subgroup.zpowers z ≤ N₁ := Subgroup.zpowers_le.2 (hRN₁ hzR)
  have hzP : IsPGroup p ↥(Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hFinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (Subgroup.zpowers z) (fixOn ρ S' Y) := by
    intro g hg w hw
    rw [mem_fixOn] at hw ⊢
    exact ⟨hY g (hzN hg).2 w hw.1, uc22p22r_fixSub_inv ρ (hzN hg).1 hw.2⟩
  obtain ⟨w₁, hw₁F, hw₁0, hw₁z⟩ := uc22p22r_exists_fixed_ne_zero ρ hp hzP hFinv (hF2 S' hS'syl)
  have hw₁R : w₁ ∈ fixSub ρ R := by
    rw [hRz, hRT, fixSub_sup]
    exact ⟨(mem_fixOn.1 hw₁F).2, hw₁z⟩
  have hZinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ Tb (fixSub ρ R) := fun s hs w hw => uc22p22r_fixSub_inv ρ (hTR hs) hw
  have hZ2 : ¬ Nat.card ↥(fixSub ρ R) ≡ 1 [MOD 2] := by
    have hord : addOrderOf (⟨w₁, hw₁R⟩ : ↥(fixSub ρ R)) = 2 := by
      refine addOrderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        show (2 : ℕ) • w₁ = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 w₁]
        rw [ZMod.natCast_self, zero_smul]
      · intro h
        exact hw₁0 (congrArg Subtype.val h)
    have hdvd : 2 ∣ Nat.card ↥(fixSub ρ R) := by
      have := addOrderOf_dvd_natCard (⟨w₁, hw₁R⟩ : ↥(fixSub ρ R))
      rwa [hord] at this
    intro hmod
    have h1 : Nat.card ↥(fixSub ρ R) % 2 = 1 := hmod
    omega
  obtain ⟨w, hwZ, hw0, hwT⟩ := uc22p22r_exists_fixed_ne_zero ρ Nat.prime_two hT2 hZinv hZ2
  refine ⟨w, hw0, fun r hr => ?_⟩
  have hw' : w ∈ fixSub ρ (R ⊔ Tb) := by
    rw [fixSub_sup]
    exact ⟨hwZ, hwT⟩
  exact hw' r hr

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
