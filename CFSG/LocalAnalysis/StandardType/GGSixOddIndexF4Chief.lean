module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestTorus
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4ChiefModule
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Ree

section Inputs

noncomputable abbrev F4Chief.reeB2Elt (K : Type) [Field K] (m : ℕ) (w : Kˣ) :
    adjointGroup ReeTag.F4.tag K :=
  F4Rest.b2TorusElt K m w

@[expose] def GGReeB2ModuleFixedInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (m : ℕ),
    Nat.card K = 2 ^ (2 * m + 1) → ∀ (p : ℕ), p.Prime → ∀ w : Kˣ, orderOf w = p →
    ∀ e : reeFixed ReeTag.F4 K m,
      (e : adjointGroup ReeTag.F4.tag K) = F4Chief.reeB2Elt K m w →
    ∀ (Q : Type) [Group Q] [Finite Q], (∀ x : Q, x ^ 2 = 1) → Nontrivial Q →
    ∀ ρ : reeFixed ReeTag.F4 K m →* MulAut Q,
      (∀ W : Subgroup Q, (∀ r, ∀ x ∈ W, ρ r x ∈ W) → W = ⊥ ∨ W = ⊤) →
        ∃ x : Q, x ≠ 1 ∧ ρ e x = x

end Inputs

namespace F4Chief

open F4Rest CFSG.SeitzReduction.F4Pilot CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Element

variable {K : Type} [Field K]

theorem units_pow_two_mul (m : ℕ) (hK : Nat.card K = 2 ^ (2 * m + 1)) (w : Kˣ) :
    w ^ (2 * 2 ^ m * 2 ^ m) = w := by
  have h1 : w ^ (Nat.card K - 1) = 1 := by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have hK1 : 1 ≤ Nat.card K := by rw [hK]; exact Nat.one_le_two_pow
  rw [show 2 * 2 ^ m * 2 ^ m = Nat.card K - 1 + 1 by rw [Nat.sub_add_cancel hK1, hK]; ring,
    pow_succ, h1, one_mul]

theorem odd_orderOf_units {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) (w : Kˣ) :
    Odd (orderOf w) := by
  have h := orderOf_dvd_natCard w
  rw [Nat.card_units, hK] at h
  refine Odd.of_dvd_nat ?_ h
  have h2 : 2 ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by rw [pow_succ, mul_comm]
  have h3 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  exact ⟨2 ^ (2 * m) - 1, by omega⟩

theorem b2TorusElt_pow_eq_one
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) {w : Kˣ} {p : ℕ} (hwp : w ^ p = 1) :
    b2TorusElt K m w ^ p = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_b2TorusElt (units_pow_two_mul m hK w), rootDiagUnit_pow,
    OneMemClass.coe_one, ← rootDiagUnit_one]
  congr 1
  funext j
  exact wu_pow_eq_one hwp (by rw [← pow_mul, mul_comm, pow_mul, hwp, one_pow]) _ _

end Element

section Torus

theorem torusElementStd_F4_explicit
    {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) {p : ℕ}
    {B : Subgroup (adjointGroup .F4 K)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ (2 * m + 1) - 1) (hB : IsElemAbelian p B) (hcard : p ^ 4 ≤ Nat.card B) :
    ∃ w : Kˣ, orderOf w = p ∧ ∃ g : adjointGroup .F4 K,
      g⁻¹ * b2TorusElt K m w * g ∈ B ∧ g⁻¹ * b2TorusElt K m w * g ≠ 1 ∧
      ∃ L₁ : Subgroup (adjointGroup .F4 K),
        IsComponentOf L₁ (Subgroup.centralizer {g⁻¹ * b2TorusElt K m w * g}) ∧
        Nat.card (B ⊓ Subgroup.centralizer (L₁ : Set (adjointGroup .F4 K)) :
          Subgroup (adjointGroup .F4 K)) ≤ p ^ 2 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have : Fact p.Prime := ⟨hp⟩
  have hpq' : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact not_three_dvd m hpq
  have hp5 : 5 ≤ p := by
    by_contra h
    push Not at h
    interval_cases p <;> simp_all (config := {decide := true})
  have hm : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    subst h0
    norm_num at hpq
    exact hp.one_lt.ne' hpq
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨g, hg⟩ := TableBF4.ggF4ToralRankInput_of_five_le hp hp5 hpq' B hB hcard
  obtain ⟨w, hw⟩ := TableBSymp.exists_orderOf_eq_of_dvd hpq'
  have hwq : w ^ (2 * 2 ^ m * 2 ^ m) = w := units_pow_two_mul m hK w
  set b₀ := b2TorusElt K m w with hb₀def
  have hb₀ : (b₀ : ModGL .F4 K) = rootDiagUnit .F4 (b2Diag w (w ^ 2 ^ m)) := coe_b2TorusElt hwq
  have hcomp := isComponentOf_B2Levi hq (rootCharKernel_b2Diag hp hp2 hw hwq) hb₀
  have hcount := card_torusPow_inf_centralizer_B2Levi_le (K := K) hp hw
  have hwp : w ^ p = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hb₀V : b₀ ∈ TableBF4.torusPow K p := by
    refine ⟨?_, Subtype.ext ?_⟩
    · rw [hb₀]
      exact f4RootDiagUnit_mem_torusGroup _
    · rw [Subgroup.coe_pow, hb₀, rootDiagUnit_pow, OneMemClass.coe_one, ← rootDiagUnit_one]
      congr 1
      funext j
      exact wu_pow_eq_one hwp (by rw [← pow_mul, mul_comm, pow_mul, hwp, one_pow]) _ _
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    have h1 : rootDiagUnit .F4 (b2Diag w (w ^ 2 ^ m)) = rootDiagUnit .F4 1 := by
      rw [← hb₀, h, rootDiagUnit_one]
      rfl
    have h2 := congrFun (rootDiagUnit_injective h1) 0
    simp [b2Diag] at h2
    rw [h2, orderOf_one] at hw
    exact hp.one_lt.ne hw
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hBV : B = (TableBF4.torusPow K p).map (MulAut.conj g⁻¹).toMonoidHom := by
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
      group
    rw [← hg, Subgroup.map_map, hid, Subgroup.map_id]
  refine ⟨w, hw, g, ?_, ?_, (B2Levi K).map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_⟩
  · rw [hBV]
    exact ⟨b₀, hb₀V, by simp [hb₀def]⟩
  · intro h
    apply hb₀1
    calc b₀ = g * (g⁻¹ * b₀ * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  · have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hinj).2 hcomp
    rwa [map_conj_centralizer_singleton, inv_inv] at h
  · rw [hBV, ← map_conj_centralizer, ← Subgroup.map_inf_eq _ _ _ hinj,
      Subgroup.card_map_of_injective hinj]
    exact hcount

theorem torusElementStd_reeB2Elt
    {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) {p : ℕ}
    {B : Subgroup (adjointGroup ReeTag.F4.tag K)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ (2 * m + 1) - 1) (hB : IsElemAbelian p B) (hcard : p ^ 4 ≤ Nat.card B) :
    ∃ w : Kˣ, orderOf w = p ∧ ∃ g : adjointGroup ReeTag.F4.tag K,
      g⁻¹ * reeB2Elt K m w * g ∈ B ∧ g⁻¹ * reeB2Elt K m w * g ≠ 1 ∧
      ∃ L₁ : Subgroup (adjointGroup ReeTag.F4.tag K),
        IsComponentOf L₁ (Subgroup.centralizer {g⁻¹ * reeB2Elt K m w * g}) ∧
        Nat.card (B ⊓ Subgroup.centralizer (L₁ : Set (adjointGroup ReeTag.F4.tag K)) :
          Subgroup (adjointGroup ReeTag.F4.tag K)) ≤ p ^ 2 :=
  torusElementStd_F4_explicit hK hp hp2 hpq hB hcard

end Torus

section Transport

variable
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem ggF4_b2Elt_conj_of_std
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) {G : Type*} [Group G]
    {ψ : adjointGroup ReeTag.F4.tag K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {p : ℕ} {Bs : Subgroup G} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ (2 * m + 1) - 1) (hBs : IsElemAbelian p Bs)
    (hcard : p ^ 4 ≤ Nat.card Bs) (hBsG : Bs ≤ ψ.range) {s : G}
    (hs : s ∈ Subgroup.normalizer (ψ.range : Set G)) (hsG : s ∉ ψ.range) (hs2 : orderOf s = 2) :
    ∃ h₀ : adjointGroup ReeTag.F4.tag K,
      (reeFixed ReeTag.F4 K m).map (ψ.comp (MulAut.conj h₀).toMonoidHom) =
        ψ.range ⊓ Subgroup.centralizer {s} ∧
      ∃ w : Kˣ, orderOf w = p ∧ ∃ b ∈ Bs, b ≠ 1 ∧
        (∃ L₁ : Subgroup G, IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2) ∧
        ∃ g ∈ ψ.range, g * b * g⁻¹ = ψ (h₀ * reeB2Elt K m w * h₀⁻¹) := by
  obtain ⟨h₀, hh₀⟩ := ggF4_exists_ree_conj hK hψ hC hs hsG hs2
  have hcardB : Nat.card (Bs.comap ψ) = Nat.card Bs := by
    rw [← Subgroup.card_map_of_injective hψ, Subgroup.map_comap_eq_self hBsG]
  obtain ⟨w, hw, g, hbB, hb1, L₁, hL₁, hL₁c⟩ :=
    torusElementStd_reeB2Elt hK hp hp2 hpq (ggF4_isElemAbelian_comap hψ hBs)
      (by rw [hcardB]; exact hcard)
  refine ⟨h₀, hh₀, w, hw, ψ (g⁻¹ * reeB2Elt K m w * g), hbB, ?_, ⟨L₁.map ψ, ?_, ?_⟩,
    ψ (h₀ * g), ⟨h₀ * g, rfl⟩, ?_⟩
  · intro h1
    exact hb1 (hψ (by rw [h1, map_one]))
  · rw [← ggF4_map_centralizer_singleton hψ]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hψ).2 hL₁
  · rw [ggF4_inf_centralizer_map hψ hBsG L₁, Subgroup.card_map_of_injective hψ]
    exact hL₁c
  · rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group

theorem ggF4_section_fixed_of_reeB2Module (hM : GGReeB2ModuleFixedInput) {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m + 1)) {G : Type} [Group G] [Finite G]
    {ψ : adjointGroup ReeTag.F4.tag K →* G} {h₀ : adjointGroup ReeTag.F4.tag K} {Y : Subgroup G}
    (hY : (reeFixed ReeTag.F4 K m).map (ψ.comp (MulAut.conj h₀).toMonoidHom) = Y)
    {p : ℕ} (hp : p.Prime) {w : Kˣ} (hw : orderOf w = p) (N V : Subgroup G) (hNV : N < V)
    (hVN : V ≤ Subgroup.normalizer (N : Set G)) (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hsq : ∀ x ∈ V, x ^ 2 ∈ N)
    (hirr : ∀ W : Subgroup G, N ≤ W → W ≤ V → Y ≤ Subgroup.normalizer (W : Set G) →
      W = N ∨ W = V) :
    ∃ v ∈ V, v ∉ N ∧ ψ (h₀ * reeB2Elt K m w * h₀⁻¹) * v *
      (ψ (h₀ * reeB2Elt K m w * h₀⁻¹))⁻¹ * v⁻¹ ∈ N := by
  set χ := (ψ.comp (MulAut.conj h₀).toMonoidHom).comp (reeFixed ReeTag.F4 K m).subtype
  have hχ : χ.range = Y := by rw [MonoidHom.range_comp, Subgroup.range_subtype, hY]
  have he : χ ⟨reeB2Elt K m w, b2TorusElt_mem_reeFixed hK w⟩ =
      ψ (h₀ * reeB2Elt K m w * h₀⁻¹) := rfl
  rw [← he]
  rw [← hχ] at hYN hYV hirr
  exact exists_fixed_of_module χ hNV hVN hYN hYV hsq hirr _
    fun Q _ _ hQ2 hQ ρ hρ => hM K m hK p hp w hw _ rfl Q hQ2 hQ ρ hρ

end Transport

end F4Chief

section Main

theorem ggSixStepThreeCFourInput_of_reeB2Module
    (hM : GGReeB2ModuleFixedInput) :
    GGSixStepThreeCFourInput := by
  have hA : GGF4AutInput := ggF4AutInput_holds
  have hI : GGF4InnerDiagInput := ggF4InnerDiagInput_holds
  have hO : GGF4GraphFieldCoreInput := ggF4GraphFieldCoreInput_holds
  have hL : GGF4TwoLocalRankInput := F4Rest.ggF4TwoLocalRankInput_holds
  intro G _ _ p B Bs x L D J n f ψ hf hctx s1 s2 _E _r _hch _hCr
  obtain ⟨⟨-, -, -, hchar, -, hp, hS, -⟩, hcore⟩ := hctx
  obtain ⟨hBs, hstd, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, ⟨hperf, hlie⟩, ⟨hBsN, hBsI⟩, -, -⟩ := hcore
  obtain ⟨hCG₀, -, hsig, -, -⟩ := s1
  set G₀ := ggG0 p B x L D J with hG₀
  set M := ggM p B x L D J with hM'
  have hcfg : GGF4Config n f ψ G₀ := ⟨hadm, hrank, hrange, hker, hperf, hlie, hCG₀⟩
  obtain ⟨hpp, hp2, -, hrk⟩ := hp
  have hBsG₀ : Bs ≤ G₀ := fun b hb => hI G n f ψ G₀ hcfg b (hBsN hb) (hBsI b hb)
  have hBG₀ : B ≤ G₀ := hBs.1.trans hBsG₀
  have hBel : IsElemAbelian p B := hS.1.1
  have hcardB : p ^ 4 ≤ Nat.card B := by
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hrk
      _ = Nat.card B := hS.1.2.1.symm
  obtain ⟨U, hU1, hU2, hBU⟩ := hS.1.2.2
  have hcop : Nat.Coprime p (Nat.card U) := by
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hpp Nat.prime_two).mpr hp2)
  have hUM : U ≤ M := hsig U (hstd.1.1.trans hBU) hcop
  have hUG : U ⊓ G₀ ≠ ⊥ := by
    intro hbot
    obtain ⟨C, -, -, hQ⟩ := hA G n f ψ G₀ hcfg hf
    obtain ⟨s, hsU, hs2, hUs⟩ := ggF4_exists_involution_of_card_le_two hU1
      (ggF4_card_le_two_of_inf_eq_bot hCG₀ hQ hUM hU2 hbot)
    have hsG₀ : s ∉ G₀ := by
      intro hs
      have hs' : s ∈ U ⊓ G₀ := ⟨hsU, hs⟩
      rw [hbot, Subgroup.mem_bot] at hs'
      rw [hs', orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
    have hBC : B ≤ Subgroup.centralizer {s} := by
      rw [hUs] at hBU
      exact hBU.trans (ggSix_normalizer_zpowers_le_centralizer hs2)
    exact ggF4_false_of_pow_le hpp (by norm_num : 3 < 4) hcardB
      (ggF4_graphField_rank_le_cube G n f ψ G₀ hcfg hf p hpp hp2 s (hUM hsU) hsG₀ hs2 B
        (le_inf hBG₀ hBC) hBel)
  have hpq : p ∣ 2 ^ f - 1 := by
    by_contra hnot
    have hBR : B ≤ Subgroup.normalizer ((U ⊓ G₀ : Subgroup G) : Set G) := fun b hb =>
      ggF4_normalizer_inf_le U G₀ ⟨hBU hb, Subgroup.le_normalizer (hBG₀ hb)⟩
    exact ggF4_false_of_pow_le hpp (by norm_num) hcardB
      (hL G n f ψ G₀ hcfg p hpp hp2 hnot (U ⊓ G₀) inf_le_right hUG (hU2.to_le inf_le_left) B
        hBG₀ hBR hBel)
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨C, hIC, hIC', -⟩ := hA G n f ψ G₀ hcfg hf
  obtain ⟨s, hsM, hsG₀, hs2⟩ :=
    ggF4_exists_involution_of_even hCG₀ Subgroup.le_normalizer le_rfl hev hIC hIC'
  have hYO := hO G n f ψ G₀ hcfg hf s hsM hsG₀ hs2
  obtain ⟨m, hm⟩ := hf
  have hK : Nat.card (GaloisField 2 f) = 2 ^ (2 * m + 1) := by
    rw [GaloisField.card 2 f (by omega), hm]
  have : CharP (GaloisField 2 f) ReeTag.F4.prime :=
    (inferInstance : CharP (GaloisField 2 f) 2)
  have hψ : Function.Injective ψ := ggF4_injective_of_center_eq_bot center_adjointGroup_eq_bot hker
  have hpq' : p ∣ 2 ^ (2 * m + 1) - 1 := hm ▸ hpq
  have hcardBs : p ^ 4 ≤ Nat.card Bs := hcardB.trans (Subgroup.card_le_of_le hBs.1)
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hCG₀
  have hBsψ : Bs ≤ ψ.range := by rw [hrange]; exact hBsG₀
  have hsψ : s ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hsM
  have hsGψ : s ∉ ψ.range := by rw [hrange]; exact hsG₀
  obtain ⟨h₀, hh₀, w, hw, b, hbBs, hb1, ⟨L₁, hL₁, hL₁c⟩, g, hgψ, hgb⟩ :=
    F4Chief.ggF4_b2Elt_conj_of_std (K := GaloisField 2 f) hK hψ hCψ hpp hp2 hpq' hBs.2.1
      hcardBs hBsψ hsψ hsGψ hs2
  have hL₁' : IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer {b}) := by rw [← hrange]; exact hL₁
  have hgG₀ : g ∈ G₀ := by rw [← hrange]; exact hgψ
  have hY : (reeFixed ReeTag.F4 (GaloisField 2 f) m).map (ψ.comp (MulAut.conj h₀).toMonoidHom) =
      G₀ ⊓ Subgroup.centralizer {s} := by rw [← hrange]; exact hh₀
  have hCb : Subgroup.centralizer {b} ≤ M :=
    (s2 b hbBs hb1 L₁ hL₁' hL₁c).2.centralizer_le (Subgroup.mem_zpowers b) hb1
  have hCe : Subgroup.centralizer {g * b * g⁻¹} ≤ M :=
    centralizer_conj_le hCb (Subgroup.le_normalizer hgG₀)
  have heY : g * b * g⁻¹ ∈ G₀ ⊓ Subgroup.centralizer {s} := by
    rw [← hY, hgb]
    exact ⟨_, F4Rest.b2TorusElt_mem_reeFixed hK w, rfl⟩
  have heodd : Odd (orderOf (g * b * g⁻¹)) := by
    rw [ggSix_orderOf_conj, ggF4_orderOf_eq_of_elemAbelian hpp hBs.2.1 hbBs hb1]
    exact hpp.odd_of_ne_two hp2
  set H := Subgroup.normalizer (Subgroup.zpowers s : Set G) with hH
  have hfix : ∀ x ∈ CFSG.Assembly.pCoreOf 2 H, x * (g * b * g⁻¹) = g * b * g⁻¹ * x →
      ∀ y ∈ G₀ ⊓ Subgroup.centralizer {s}, x * y = y * x := fun x hx hxe y hy =>
    ggSix_commute_of_mem_pCoreOf_inf (M := M) hs2 inf_le_right hYO
      (ggSix_inf_centralizer_le_normalizer G₀ s)
      ⟨hx, hCe (Subgroup.mem_centralizer_singleton_iff.mpr hxe)⟩ hy
  have hYH : G₀ ⊓ Subgroup.centralizer {s} ≤ H :=
    inf_le_right.trans (ggSix_centralizer_le_normalizer_zpowers s)
  have hcent := ggF4_centralizes_of_chiefFactor (Y := G₀ ⊓ Subgroup.centralizer {s}) heodd
    (fun N V hNV _ hVN hYN hYV hsq hirr => by
      rw [hgb]
      exact F4Chief.ggF4_section_fixed_of_reeB2Module hM hK hY hpp hw N V hNV hVN hYN hYV hsq
        hirr)
    (CFSG.Assembly.pCoreOf 2 H) (ggSix_pCoreOf_isPGroup 2 H)
    (hYH.trans (ggSix_le_normalizer_pCoreOf 2 H)) hfix
  have heP : g * b * g⁻¹ ∈ CFSG.Assembly.pCoreOf 2 H :=
    hchar H (ggSix_isTwoLocal_normalizer_zpowers hs2)
      ⟨hYH heY, Subgroup.mem_centralizer_iff.mpr hcent⟩
  have he1 := ggSix_eq_one_of_mem_of_odd (ggSix_pCoreOf_isPGroup 2 H) heP heodd
  apply hb1
  calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
    _ = 1 := by rw [he1]; group

end Main

end CFSG.StandardType
