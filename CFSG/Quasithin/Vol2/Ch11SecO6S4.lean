module

public import CFSG.Quasithin.Vol2.Ch11SecO6S3
public import CFSG.Quasithin.Vol2.Ch11SecO6S2
public import CFSG.Quasithin.Vol2.Ch11SecO7a

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecG.Bar
open CFSG.Quasithin.Vol2.Ch11.O6
open scoped MatrixGroups

section Quot

variable {G : Type} [Group G] {K : Subgroup G} {p : ℕ}

theorem exists_kBar_hom {φK : ↥K →* SL(2, ZMod p)} (hs : Function.Surjective φK)
    (hk : φK.ker = (oTwoTwoPrime K).subgroupOf K) :
    ∃ φ : KBar K →* SL(2, ZMod p), Function.Surjective φ ∧
      φ.ker = CFSG.oddCore (KBar K) ∧ ∀ k : ↥K, φ (k : KBar K) = φK k := by
  have hle : CFSG.pCore 2 ↥K ≤ φK.ker := by
    intro x hx
    rw [hk, Subgroup.mem_subgroupOf, mem_oTwoTwoPrime_iff, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  refine ⟨QuotientGroup.lift _ φK hle, ?_, ?_, fun k => QuotientGroup.lift_mk _ hle k⟩
  · intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨x, QuotientGroup.lift_mk _ hle x⟩
  · ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, ← MonoidHom.mem_ker, hk,
      Subgroup.mem_subgroupOf, mem_oTwoTwoPrime_iff, QuotientGroup.mk'_apply]

theorem inv_mul_aut_mem_oddCore {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ oTwoTwoPrime K) (x : KBar K) :
    x⁻¹ * aut K ⟨a, ha⟩ x ∈ CFSG.oddCore (KBar K) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 := (mem_oTwoTwoPrime_iff (⟨a * k * a⁻¹ * (k : G)⁻¹, commK_mem ha k.2⟩ : ↥K)).mp
    (h k k.2)
  rw [QuotientGroup.mk'_apply, mk_commK ha k.2] at h1
  have h2 := (CFSG.oddCore_normal (KBar K)).conj_mem _ h1 ((k : KBar K))⁻¹
  convert h2 using 1
  group

end Quot

theorem sub_one_mul_sub_one_mod {r : ℕ} (hr : 2 ≤ r) : (r - 1) * (r - 1) % r = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have e : (m + 2 - 1) * (m + 2 - 1) = 1 + (m + 2) * m := by
    rw [show m + 2 - 1 = m + 1 by omega]
    ring
  rw [e, Nat.add_mul_mod_self_left]
  exact Nat.one_mod_eq_one.mpr (by omega)

section M2


theorem factM2Case1_holds : FactM2Case1 := by
  intro G _ _ K L₁ R n hlist h1 ⟨r, hr, hFr⟩ hL₁K hperf ⟨F₄, _, _, hF₄, ⟨eL⟩⟩ _ hRK hRL hRL₁
    A hAR hA
  obtain ⟨p, hp, hp5', φK, hφKs, hφKk⟩ := h1
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by rcases hp5' with h | h <;> omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨φ, hφs, hφk, -⟩ := exists_kBar_hom hφKs hφKk
  have hn : n = 2 := by
    rcases hlist with h | ⟨h, -⟩
    · exact (false_of_list2 h hp2 hφs).elim
    · exact h
  subst hn
  have hF₄' : Nat.card F₄ = 4 := by rw [hF₄]; norm_num
  have h60 := index_pCore_eq_sixty hF₄' eL
  have hsh := shape_of_lists hlist hp2 hφs
  have hD : Case1Data (KBar K) := case1Data_of_shape hsh
  have hOF : CFSG.oddCore (KBar K) = CFSG.fittingSubgroup (KBar K) := oddCore_eq hD
  have : Fact r.Prime := ⟨hr⟩
  have hFne : CFSG.fittingSubgroup (KBar K) ≠ ⊥ := by
    intro hbot
    obtain ⟨y, hy⟩ := hφs (-1)
    have hyF : y ∈ CFSG.fittingSubgroup (KBar K) := by
      apply hD.struct.1
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      rw [hbot, SetLike.mem_coe, Subgroup.mem_bot] at hf
      rw [hf, one_mul, mul_one]
    rw [hbot, Subgroup.mem_bot] at hyF
    rw [hyF, map_one] at hy
    exact neg_one_ne_one (two_ne_zero_zmod hp5) hy.symm
  have hrF : r ∣ Nat.card (CFSG.fittingSubgroup (KBar K)) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hFr
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hm
      exact hFne (Subgroup.eq_bot_of_card_eq _ hm)
    rw [hm]
    exact dvd_pow_self r hm0
  have hr2 : r ≠ 2 := by
    have := hD.struct.2.1 r hr hrF
    omega
  have hPF : CFSG.pCore r (KBar K) = CFSG.fittingSubgroup (KBar K) :=
    le_antisymm (CFSG.pCore_le_fitting _ r) (le_sSup ⟨inferInstance, hFr⟩)
  have hFt : ∀ f ∈ CFSG.fittingSubgroup (KBar K),
      ActsTriviallyOnFrattiniQuotient (CFSG.pCore r (KBar K)) f := fun f hf =>
    fitting_acts_triv r hf
  have hna := exists_not_triv r hD hrF (Or.inr hFr)
  obtain ⟨s, hsL, hφs1, -, -⟩ := exists_s hp5 hφk hL₁K hperf h60
  have hfixL : ∀ a (ha : a ∈ R), ∀ x ∈ l1Bar K L₁, aut K ⟨a, hRK ha⟩ x = x := fun a ha =>
    aut_eq_self_of_comm hp5 hφk hL₁K hperf h60 (hRK ha)
      (fun l hl => hRL₁ (Subgroup.commutator_mem_commutator ha hl))
  have hRK₂ := SecE.sl2pSignalizerFact_holds G K L₁ R p hp hp5' ⟨φK, hφKs, hφKk⟩ hL₁K hperf
    ⟨F₄, inferInstance, inferInstance, hF₄', ⟨eL⟩⟩ hRK hRL hRL₁
  have hcomm : ∀ a (ha : a ∈ R) (x : KBar K),
      x⁻¹ * aut K ⟨a, hRK ha⟩ x ∈ CFSG.fittingSubgroup (KBar K) := fun a ha x => by
    rw [← hOF]
    exact inv_mul_aut_mem_oddCore (hRK ha)
      (fun k hk => hRK₂ (Subgroup.commutator_mem_commutator ha hk)) x
  have htriv : ∀ a (ha : a ∈ R), (aut K ⟨a, hRK ha⟩) ^ 2 ^ 1 = 1 →
      ActsScalar r (aut K ⟨a, hRK ha⟩) 1 → ∀ x, aut K ⟨a, hRK ha⟩ x = x := by
    intro a ha ha2 h1' x
    have hfixF : ∀ f ∈ CFSG.fittingSubgroup (KBar K), aut K ⟨a, hRK ha⟩ f = f := fun f hf =>
      fix_of_actsScalar_one r hr2 ha2 h1' f (hPF ▸ hf)
    rcases hsh with h4 | ⟨q, hq, hq5, -, -, hE, hN⟩
    · have hp5eq : p = 5 := A313.p_eq_five_of_case4 hOF.symm h4 hp
        ⟨(QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩
      subst hp5eq
      obtain ⟨-, hcard⟩ := range_spec hp5 hφk hL₁K hperf h60
      have htop : (φ.comp (l1Map hL₁K)).range = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hcard, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
        norm_num
      obtain ⟨l, hl⟩ : φ x ∈ (φ.comp (l1Map hL₁K)).range := htop ▸ Subgroup.mem_top _
      have hf : (l1Map hL₁K l)⁻¹ * x ∈ CFSG.fittingSubgroup (KBar K) := by
        rw [← hOF, ← hφk, MonoidHom.mem_ker, map_mul, map_inv]
        rw [MonoidHom.comp_apply] at hl
        rw [hl, inv_mul_cancel]
      calc aut K ⟨a, hRK ha⟩ x =
          aut K ⟨a, hRK ha⟩ (l1Map hL₁K l * ((l1Map hL₁K l)⁻¹ * x)) := by
            rw [mul_inv_cancel_left]
        _ = l1Map hL₁K l * ((l1Map hL₁K l)⁻¹ * x) := by
          rw [map_mul, hfixL a ha _ (l1Map_mem hL₁K l), hfixF _ hf]
        _ = x := mul_inv_cancel_left _ _
    · have : Fact q.Prime := ⟨hq⟩
      have hq11 := SecE.eleven_le_of_mod_five hq hq5
      have hsF : s ∉ CFSG.fittingSubgroup (KBar K) := by
        rw [← hOF, ← hφk, MonoidHom.mem_ker, hφs1]
        exact neg_one_ne_one (two_ne_zero_zmod hp5)
      have hs2 : s ^ 2 ∈ CFSG.fittingSubgroup (KBar K) := by
        rw [← hOF, ← hφk, MonoidHom.mem_ker, map_pow, hφs1, neg_one_sq]
      obtain ⟨eF⟩ := hE
      have hab : ∀ u ∈ CFSG.fittingSubgroup (KBar K), ∀ v ∈ CFSG.fittingSubgroup (KBar K),
          u * v = v * u := fun u hu v hv => by
        have h := congrArg Subtype.val (eF.injective (show eF (⟨u, hu⟩ * ⟨v, hv⟩) =
          eF (⟨v, hv⟩ * ⟨u, hu⟩) by rw [map_mul, map_mul, mul_comm]))
        simpa using h
      have hodd : Odd (Nat.card (CFSG.fittingSubgroup (KBar K))) := by
        rw [← hOF]
        exact Quasithin.A312.odd_card_oddCore _
      have hsc : ∀ y : KBar K, (s * y)⁻¹ * (y * s) ∈ CFSG.fittingSubgroup (KBar K) := by
        intro y
        rw [← hOF, ← hφk, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hφs1,
          neg_one_mul, mul_neg_one, inv_mul_cancel]
      exact eq_self_of_inverts hodd hab
        (conj_eq_inv_of_natural (two_ne_zero_zmod (by omega)) hN hsF hs2) hsc hfixF
        (hfixL a ha s hsL) (hcomm a ha) x
  have hαsq : ∀ a (ha : a ∈ A), (aut K ⟨a, hRK (hAR ha)⟩) ^ 2 ^ 1 = 1 := fun a ha => by
    rw [pow_one, ← map_pow]
    have : (⟨a, hRK (hAR ha)⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 = 1 :=
      Subtype.ext (by simp [hA.2 a ha])
    rw [this, map_one]
  have hsign : ∀ a (ha : a ∈ A), ActsScalar r (aut K ⟨a, hRK (hAR ha)⟩) 1 ∨
      ActsScalar r (aut K ⟨a, hRK (hAR ha)⟩) (r - 1) := by
    intro a ha
    obtain ⟨k, hk⟩ := actsScalar_of_comm r (hD.rank r hr hrF) hFt hna (hcomm a (hAR ha))
    have h2 : ActsScalar r ((aut K ⟨a, hRK (hAR ha)⟩) ^ 2) 1 := by
      have h := hαsq a ha
      rw [pow_one] at h
      rw [h]
      intro d _
      simp
    exact actsScalar_sign r hk h2
  have hinC : ∀ a (ha : a ∈ A), ActsScalar r (aut K ⟨a, hRK (hAR ha)⟩) 1 →
      a ∈ sectionCentralizer K (pCoreOf 2 K) := fun a ha h =>
    mem_sectionCentralizer_of_aut (hRK (hAR ha)) (htriv a (hAR ha) (hαsq a ha) h)
  refine mQuot_le_one_of fun a ha b hb haC hbC => ?_
  have hna' := (hsign a ha).resolve_left fun h => haC (hinC a ha h)
  have hnb' := (hsign b hb).resolve_left fun h => hbC (hinC b hb h)
  have hmul : aut K ⟨a * b, hRK (hAR (A.mul_mem ha hb))⟩ =
      aut K ⟨a, hRK (hAR ha)⟩ * aut K ⟨b, hRK (hAR hb)⟩ := by
    rw [← map_mul]
    rfl
  refine hinC (a * b) (A.mul_mem ha hb) ?_
  rw [hmul]
  exact actsScalar_one_of_mod (ActsScalar.mul r hna' hnb')
    (sub_one_mul_sub_one_mod (Fact.out : r.Prime).two_le)

end M2

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
