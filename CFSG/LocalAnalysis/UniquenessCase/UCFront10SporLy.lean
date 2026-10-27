module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017LyFive
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InThompson
import CFSG.LocalAnalysis.UniquenessCase.UCFront10Alt
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T4
import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG CFSG.QuasithinUnique Subgroup CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

section Basic


theorem ly_card_le_sixteen (E : Subgroup J) (hES : E ≤ lyS)
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h64 : Nat.card ↥(lyE1 ⊔ lyE2) = 64 := by
    rw [← lyQ_subgroupOf, ← card_lyQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe lyQ_le).toEquiv
  have h32 : ∀ F : Subgroup lyS, CFSG.Open.IsElemAbelian 2 F → Nat.card F ≠ 32 := by
    intro F hF hF32
    have : CFSG.IsElementaryAbelian 2 ↥F := hF.isElementaryAbelian
    have hexp : Monoid.exponent ↥F ∣ 2 := CFSG.IsElementaryAbelian.exponent_dvd_p 2 ↥F
    have h16 : ∀ H : Subgroup ↥F, H.index = 2 →
        H.map F.subtype = lyE1 ∨ H.map F.subtype = lyE2 := by
      intro H hH
      apply (ea16_iff _).1
      refine ⟨(hF.mono (Subgroup.map_subtype_le H)).isElementaryAbelian, ?_⟩
      rw [Subgroup.card_map_of_injective F.subtype_injective]
      have := Subgroup.card_mul_index H
      rw [hH, hF32] at this
      omega
    have hFne : (⊤ : Subgroup ↥F) ≠ ⊥ := by
      intro h
      have := Subgroup.card_top (G := ↥F)
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨σ, -, hσ⟩ := (Subgroup.bot_or_exists_ne_one (⊤ : Subgroup ↥F)).resolve_left hFne
    obtain ⟨H₁, hH₁, hσH₁⟩ := TauCeti.exists_index_eq_two_notMem_of_exponent_dvd_two hexp hσ
    have hH₁ne : H₁ ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.index_bot, hF32] at hH₁
      omega
    obtain ⟨τ, hτH₁, hτ⟩ := (Subgroup.bot_or_exists_ne_one H₁).resolve_left hH₁ne
    obtain ⟨H₂, hH₂, hτH₂⟩ := TauCeti.exists_index_eq_two_notMem_of_exponent_dvd_two hexp hτ
    have hne : H₁.map F.subtype ≠ H₂.map F.subtype := by
      intro h
      have hmem : (τ : lyS) ∈ H₁.map F.subtype := ⟨τ, hτH₁, rfl⟩
      rw [h] at hmem
      obtain ⟨y, hy, hyτ⟩ := hmem
      have hyτ' : y = τ := Subtype.ext hyτ
      exact hτH₂ (hyτ' ▸ hy)
    have h1 : H₁.map F.subtype ≤ F := Subgroup.map_subtype_le H₁
    have h2 : H₂.map F.subtype ≤ F := Subgroup.map_subtype_le H₂
    have hle : lyE1 ⊔ lyE2 ≤ F := by
      rcases h16 H₁ hH₁ with e1 | e1 <;> rcases h16 H₂ hH₂ with e2 | e2
      · exact absurd (e1.trans e2.symm) hne
      · rw [e1] at h1
        rw [e2] at h2
        exact sup_le h1 h2
      · rw [e1] at h1
        rw [e2] at h2
        exact sup_le h2 h1
      · exact absurd (e1.trans e2.symm) hne
    have := Subgroup.card_dvd_of_le hle
    rw [h64, hF32] at this
    norm_num at this
  have hE'c : Nat.card ↥(E.subgroupOf lyS) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  have hE'e : CFSG.Open.IsElemAbelian 2 (E.subgroupOf lyS) := hE.subgroupOf lyS
  obtain ⟨k, hk⟩ := hE'e.isPGroup.exists_card_eq
  by_contra hlt
  have hk5 : 5 ≤ k := by
    by_contra h
    have h16 : Nat.card ↥E ≤ 16 := by
      rw [← hE'c, hk]
      calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 16 := by norm_num
    exact hlt h16
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(E.subgroupOf lyS)) 2 (n := 5)
    (by rw [hk]; exact pow_dvd_pow 2 hk5)
  exact h32 (K.map (E.subgroupOf lyS).subtype) (hE'e.mono (Subgroup.map_subtype_le K))
    (by rw [Subgroup.card_map_of_injective (E.subgroupOf lyS).subtype_injective, hK]; norm_num)

theorem ly_thompsonJ_eq : CFSG.Quasithin.thompsonJ lyS = lyQ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEi : ∀ Ei : Subgroup lyS, (Ei = lyE1 ∨ Ei = lyE2) →
      CFSG.Open.IsElemAbelian 2 (Ei.map lyS.subtype) ∧ Nat.card (Ei.map lyS.subtype) = 16 := by
    intro Ei hEi
    obtain ⟨hea, hc⟩ := (ea16_iff Ei).2 hEi
    refine ⟨(CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hea).map lyS.subtype, ?_⟩
    rw [Subgroup.card_map_of_injective lyS.subtype_injective, hc]
  have hQ : lyQ = lyE1.map lyS.subtype ⊔ lyE2.map lyS.subtype := by
    rw [lyQ_eq, Subgroup.map_sup]
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hA16 : Nat.card A = 16 := by
      refine le_antisymm (ly_card_le_sixteen A hA.1 hA.2.1) ?_
      have h := hA.2.2 _ (Subgroup.map_subtype_le lyE1) (hEi lyE1 (Or.inl rfl)).1
      rwa [(hEi lyE1 (Or.inl rfl)).2] at h
    have hA' : A.subgroupOf lyS = lyE1 ∨ A.subgroupOf lyS = lyE2 := by
      apply (ea16_iff _).1
      refine ⟨(hA.2.1.subgroupOf lyS).isElementaryAbelian, ?_⟩
      rw [← hA16]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
    rw [← Subgroup.map_subgroupOf_eq_of_le hA.1, hQ]
    rcases hA' with h | h <;> rw [h]
    · exact le_sup_left
    · exact le_sup_right
  · refine le_thompsonJ_of_rank (m := 4) lyQ_le (fun A hA hAe => ly_card_le_sixteen A hA hAe) ?_
    have h1 : lyE1.map lyS.subtype ≤ lyQ := by rw [hQ]; exact le_sup_left
    have h2 : lyE2.map lyS.subtype ≤ lyQ := by rw [hQ]; exact le_sup_right
    calc lyQ = lyE1.map lyS.subtype ⊔ lyE2.map lyS.subtype := hQ
      _ ≤ _ := sup_le
          (le_iSup₂_of_le (lyE1.map lyS.subtype)
            ⟨h1, (hEi _ (Or.inl rfl)).1, (hEi _ (Or.inl rfl)).2⟩ le_rfl)
          (le_iSup₂_of_le (lyE2.map lyS.subtype)
            ⟨h2, (hEi _ (Or.inr rfl)).1, (hEi _ (Or.inr rfl)).2⟩ le_rfl)

end Basic

section Centralizer


theorem ly_k105In_centralizer : K105In (centralizer {lyz}) lyS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf lyS ⊤ := ⟨le_top, lySylow.isPGroup', by
    change ¬ 2 ∣ lyS.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact lySylow.not_dvd_index⟩
  have hzc : zS ∈ center ↥lyS := by
    rw [center_lyS]
    exact Subgroup.mem_zpowers _
  have hSC : lyS ≤ centralizer {lyz} := fun s hs => by
    have h := Subgroup.mem_center_iff.1 hzc ⟨s, hs⟩
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact Subgroup.mem_centralizer_singleton_iff.2 h
  have hz2 : orderOf lyz = 2 := (Subgroup.orderOf_coe zS).trans orderOf_zS
  have hK : CFSG.Blueprint.NativeSporadic.IsSporadic ↥J .Ly := ⟨lyEquivJ.symm⟩
  obtain ⟨-, hZ2, ⟨e⟩⟩ := involution_centralizers_quasisimple hK lyz hz2
  refine k105In_of_quotient hS hSC (center ↥(centralizer {lyz})) ?_ e
    fun S H hS' hSH _ h3 => le_of_isSylowTwoOf_of_not_three_dvd_alt (by norm_num)
      (MulEquiv.refl _) hS' hSH h3
  rintro _ ⟨x, hx, rfl⟩
  have hzC : lyz ∈ centralizer {lyz} := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzZ : (⟨lyz, hzC⟩ : ↥(centralizer {lyz})) ∈ center ↥(centralizer {lyz}) := by
    rw [Subgroup.mem_center_iff]
    intro g
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
    have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    exact h
  have hz1 : (⟨⟨lyz, hzC⟩, hzZ⟩ : ↥(center ↥(centralizer {lyz}))) ≠ 1 := by
    intro h
    rw [Subgroup.mk_eq_one, Subgroup.mk_eq_one] at h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(center ↥(centralizer {lyz})))).1 hZ2
  rw [Subgroup.coe_subtype]
  by_cases hx1 : (⟨x, hx⟩ : ↥(center ↥(centralizer {lyz}))) = 1
  · rw [Subgroup.mk_eq_one] at hx1
    rw [hx1, Subgroup.coe_one]
    exact lyS.one_mem
  · have h' : x = ⟨lyz, hzC⟩ := congrArg Subtype.val ((hy _ hx1).trans (hy _ hz1).symm)
    rw [h']
    exact lyz_mem_lyS

end Centralizer

section Five


theorem ly_oddLocal (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : Subgroup J)
    (hA : CFSG.Open.IsElemAbelian p A) (hA1 : A ≠ ⊥) (hSA : lyS ≤ normalizer (A : Set J)) :
    A ⊓ centralizer {lyz} ≠ ⊥ := by
  intro hAz
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian p ↥A := hA.isElementaryAbelian
  obtain ⟨n, hn⟩ := hA.isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, Commute a b := fun a ha b hb => by
    have h := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  have hnormA : ∀ g ∈ lyS, ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.1 (hSA hg) a).1 ha
  have hz2 : orderOf lyz = 2 := (Subgroup.orderOf_coe zS).trans orderOf_zS
  have hzz : lyz * lyz = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzinv : lyz⁻¹ = lyz := inv_eq_of_mul_eq_one_right hzz
  have hinv : ∀ a ∈ A, lyz * a * lyz⁻¹ = a⁻¹ := by
    intro a ha
    have hw : lyz * a * lyz⁻¹ ∈ A := hnormA _ lyz_mem_lyS a ha
    have hb : a * (lyz * a * lyz⁻¹) ∈ A ⊓ centralizer {lyz} := by
      refine Subgroup.mem_inf.2 ⟨A.mul_mem ha hw, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := (hAcomm a ha _ hw).eq
      rw [hzinv] at hc ⊢
      calc a * (lyz * a * lyz) * lyz = lyz * a * lyz * a * lyz := by rw [hc]
        _ = lyz * (a * (lyz * a * lyz)) := by group
    rw [hAz] at hb
    exact eq_inv_of_mul_eq_one_right (Subgroup.mem_bot.1 hb)
  have hfaith : ∀ g ∈ lyS, (∀ x ∈ A, g * x * g⁻¹ = x) → g = 1 := by
    intro g hg hgA
    by_contra hg1
    obtain ⟨K, hKdef⟩ : ∃ K : Subgroup ↥lyS, K = (centralizer (A : Set J)).subgroupOf lyS :=
      ⟨_, rfl⟩
    have hKn : K.Normal := by
      constructor
      intro k hk s
      rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hk ⊢
      intro a ha
      have ha' : (s : J)⁻¹ * a * (s : J) ∈ A := by
        have h := hnormA _ (lyS.inv_mem s.2) a ha
        rwa [inv_inv] at h
      have hka := hk _ ha'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      calc a * ((s : J) * (k : J) * (s : J)⁻¹)
          = (s : J) * (((s : J)⁻¹ * a * (s : J)) * (k : J)) * (s : J)⁻¹ := by group
        _ = (s : J) * ((k : J) * ((s : J)⁻¹ * a * (s : J))) * (s : J)⁻¹ := by rw [hka]
        _ = ((s : J) * (k : J) * (s : J)⁻¹) * a := by group
    have hK1 : K ≠ ⊥ := by
      intro h
      have hgK : (⟨g, hg⟩ : ↥lyS) ∈ K := by
        rw [hKdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro a ha
        exact (mul_inv_eq_iff_eq_mul.1 (hgA a ha)).symm
      rw [h] at hgK
      exact hg1 ((Subgroup.mk_eq_one _).1 (Subgroup.mem_bot.1 hgK))
    have : Group.IsNilpotent ↥lyS := lySylow.isPGroup'.isNilpotent
    have hKZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hK1
    rw [center_lyS] at hKZ
    obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hKZ
    have hxz : x = zS := (mem_zpowers_zS.1 (Subgroup.mem_inf.1 hx).2).resolve_left hx1
    have hzK : zS ∈ K := by
      rw [← hxz]
      exact (Subgroup.mem_inf.1 hx).1
    rw [hKdef, Subgroup.mem_subgroupOf] at hzK
    apply hA1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have hza : a * lyz = lyz * a := (Subgroup.mem_centralizer_iff.1 hzK) a ha
    have h1 : a⁻¹ = a := by rw [← hinv a ha, ← hza, mul_inv_cancel_right]
    have ha2 : a ^ 2 = 1 := by
      calc a ^ 2 = a⁻¹ * a := by rw [h1, pow_two]
        _ = 1 := inv_mul_cancel a
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_of_pow_eq_one (hA.2 a ha)))
  have h256 : 256 ∣ Nat.card (GL (Fin n) (ZMod p)) := by
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm2.L915.card_dvd_card_GL_of_faithful hp
      (P := A) (E := lyS) hn hnormA hfaith
    rwa [card_lyS] at h
  rcases Nat.lt_or_ge p 7 with hp7 | hp7
  ·
    obtain rfl : p = 5 := by
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    have hK : CFSG.Blueprint.NativeSporadic.IsSporadic ↥J .Ly := ⟨lyEquivJ.symm⟩
    obtain ⟨hE1ea, hE1c⟩ := (ea16_iff lyE1).2 (Or.inl rfl)
    obtain ⟨E, hEdef⟩ : ∃ E : Subgroup J, E = lyE1.map lyS.subtype := ⟨_, rfl⟩
    have hEe : CFSG.Open.IsElemAbelian 2 E := by
      rw [hEdef]
      exact (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hE1ea).map lyS.subtype
    have hEc : Nat.card E = 16 := by
      rw [hEdef, Subgroup.card_map_of_injective lyS.subtype_injective, hE1c]
    have hES : E ≤ lyS := by
      rw [hEdef]
      exact Subgroup.map_subtype_le lyE1
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, Commute a b := fun a ha b hb => by
      have h := hEe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h
      exact h
    have hzE : lyz ∈ E := by
      have h6 : sE 6 ∈ lyE1 := ((lists_eaSub e16a_mem).2 6 (by norm_num)).1 (by decide)
      rw [← zS_eq] at h6
      rw [hEdef]
      exact ⟨zS, h6, rfl⟩
    obtain ⟨e, hedef⟩ : ∃ e : J, e = ((sE 3 : lyS) : J) := ⟨_, rfl⟩
    have heE : e ∈ E := by
      have h3 : sE 3 ∈ lyE1 := ((lists_eaSub e16a_mem).2 3 (by norm_num)).1 (by decide)
      rw [hEdef, hedef]
      exact ⟨sE 3, h3, rfl⟩
    have he1 : e ≠ 1 := by
      intro h
      rw [hedef] at h
      have h' : sE 3 = sE 0 := by
        rw [sE_zero]
        exact OneMemClass.coe_eq_one.1 h
      exact absurd (sE_inj (by norm_num) (by norm_num) h') (by norm_num)
    have hez : e ≠ lyz := by
      intro h
      rw [hedef] at h
      have h' : sE 3 = sE 6 := by
        rw [← zS_eq]
        exact Subtype.ext h
      exact absurd (sE_inj (by norm_num) (by norm_num) h') (by norm_num)
    have hF5 : ∀ t ∈ E, t ≠ 1 → Nat.card ↥(A ⊓ centralizer {t}) ≤ 5 := by
      intro t htE ht1
      have ht2 : orderOf t = 2 := orderOf_eq_prime (hEe.2 t htE) ht1
      obtain ⟨hda, hdb⟩ := CFSG.LocalAnalysis.GLTheoremA.H1017.ly_involution_data_five hK ht2
      have hFe : CFSG.Open.IsElemAbelian 5 (A ⊓ centralizer {t}) := hA.mono inf_le_left
      have h25 := hda _ inf_le_right hFe
      obtain ⟨k, hk⟩ := hFe.isPGroup.exists_card_eq
      rw [hk] at h25 ⊢
      have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h25
      have hk2' : k ≠ 2 := by
        rintro rfl
        have : CFSG.IsElementaryAbelian 5 ↥(A ⊓ centralizer {t}) := hFe.isElementaryAbelian
        have : CFSG.IsElementaryAbelian 2 ↥E := hEe.isElementaryAbelian
        obtain ⟨H, hH2, htH⟩ := TauCeti.exists_index_eq_two_notMem_of_exponent_dvd_two
          (CFSG.IsElementaryAbelian.exponent_dvd_p 2 ↥E) (σ := (⟨t, htE⟩ : ↥E))
          (fun h => ht1 (congrArg Subtype.val h))
        have hH8 : Nat.card ↥(H.map E.subtype) = 8 := by
          rw [Subgroup.card_map_of_injective E.subtype_injective]
          have := Subgroup.card_mul_index H
          rw [hH2, hEc] at this
          omega
        have hnormH : ∀ u ∈ H.map E.subtype, ∀ x ∈ A ⊓ centralizer {t},
            u * x * u⁻¹ ∈ A ⊓ centralizer {t} := by
          rintro _ ⟨u, -, rfl⟩ x hx
          rw [Subgroup.coe_subtype]
          obtain ⟨hxA, hxt⟩ := Subgroup.mem_inf.1 hx
          have hut : (u : J) * t = t * u := (hEcomm _ u.2 _ htE).eq
          have hxt' := Subgroup.mem_centralizer_singleton_iff.1 hxt
          have hut' : (u : J)⁻¹ * t = t * (u : J)⁻¹ := by
            calc (u : J)⁻¹ * t = (u : J)⁻¹ * (t * u) * (u : J)⁻¹ := by group
              _ = (u : J)⁻¹ * (u * t) * (u : J)⁻¹ := by rw [hut]
              _ = t * (u : J)⁻¹ := by group
          refine Subgroup.mem_inf.2 ⟨hnormA _ (hES u.2) x hxA, ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (u : J) * x * (u : J)⁻¹ * t = (u : J) * x * ((u : J)⁻¹ * t) := by group
            _ = (u : J) * x * (t * (u : J)⁻¹) := by rw [hut']
            _ = (u : J) * (x * t) * (u : J)⁻¹ := by group
            _ = (u : J) * (t * x) * (u : J)⁻¹ := by rw [hxt']
            _ = ((u : J) * t) * x * (u : J)⁻¹ := by group
            _ = (t * (u : J)) * x * (u : J)⁻¹ := by rw [hut]
            _ = t * ((u : J) * x * (u : J)⁻¹) := by group
        have hinvH : ∀ u ∈ H.map E.subtype, u * u = 1 := by
          rintro _ ⟨u, -, rfl⟩
          rw [Subgroup.coe_subtype, ← pow_two]
          exact hEe.2 _ u.2
        have hfaithH : ∀ u ∈ H.map E.subtype,
            (∀ x ∈ A ⊓ centralizer {t}, u * x * u⁻¹ = x) → u = 1 := by
          rintro _ ⟨u, huH, rfl⟩ hux
          rw [Subgroup.coe_subtype] at hux ⊢
          by_contra hu1
          have hu2 : orderOf (u : J) = 2 := orderOf_eq_prime (hEe.2 _ u.2) hu1
          have hucent : (u : J) ∈ centralizer ((A ⊓ centralizer {t} : Subgroup J) : Set J) :=
            Subgroup.mem_centralizer_iff.2 fun x hx => (mul_inv_eq_iff_eq_mul.1 (hux x hx)).symm
          have hut : (u : J) = t :=
            hdb _ inf_le_right hFe hk (u : J) hu2 hucent (hEcomm _ u.2 _ htE).eq
          apply htH
          have hu : u = ⟨t, htE⟩ := Subtype.ext hut
          rw [← hu]
          exact huH
        have hle := CFSG.GH74.GLS.Stage2.Bender.Thm2.L915.card_le_four_of_faithful_p_sq
          (by norm_num : Nat.Prime 5) (by norm_num) hk hnormH hinvH hfaithH
        omega
      calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 5 := by norm_num
    have hze : lyz * e ∈ E := E.mul_mem hzE heE
    have hze1 : lyz * e ≠ 1 := by
      intro h
      apply hez
      calc e = lyz⁻¹ * (lyz * e) := by group
        _ = lyz⁻¹ := by rw [h, mul_one]
        _ = lyz := hzinv
    have hc1 := hF5 e heE he1
    have hc2 := hF5 (lyz * e) hze hze1
    have hee : e * e = 1 := by
      rw [← pow_two]
      exact hEe.2 e heE
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
    have hw : ∀ a ∈ A, e * a * e⁻¹ ∈ A := fun a ha => hnormA e (hES heE) a ha
    have hwa : ∀ a : J, e * (e * a * e⁻¹) * e⁻¹ = a := by
      intro a
      rw [heinv]
      calc e * (e * a * e) * e = (e * e) * a * (e * e) := by group
        _ = a := by rw [hee, one_mul, mul_one]
    have hm1 : ∀ a ∈ A, (a * (e * a * e⁻¹)) ^ 3 ∈ A ⊓ centralizer {e} := by
      intro a ha
      refine Subgroup.mem_inf.2 ⟨A.pow_mem (A.mul_mem ha (hw a ha)) 3, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := hAcomm a ha _ (hw a ha)
      have hX : e * (a * (e * a * e⁻¹)) * e⁻¹ = a * (e * a * e⁻¹) :=
        calc e * (a * (e * a * e⁻¹)) * e⁻¹
            = (e * a * e⁻¹) * (e * (e * a * e⁻¹) * e⁻¹) := by group
          _ = (e * a * e⁻¹) * a := by rw [hwa]
          _ = a * (e * a * e⁻¹) := hc.eq.symm
      have hconj : e * (a * (e * a * e⁻¹)) ^ 3 * e⁻¹ = (a * (e * a * e⁻¹)) ^ 3 := by
        rw [← conj_pow, hX]
      calc (a * (e * a * e⁻¹)) ^ 3 * e
          = e * (a * (e * a * e⁻¹)) ^ 3 * e⁻¹ * e := by rw [hconj]
        _ = e * (a * (e * a * e⁻¹)) ^ 3 := by group
    have hm2 : ∀ a ∈ A, (a * (e * a * e⁻¹)⁻¹) ^ 3 ∈ A ⊓ centralizer {lyz * e} := by
      intro a ha
      refine Subgroup.mem_inf.2 ⟨A.pow_mem (A.mul_mem ha (A.inv_mem (hw a ha))) 3, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (lyz * e) * a * (lyz * e)⁻¹ = (e * a * e⁻¹)⁻¹ := by
        rw [mul_inv_rev lyz e,
          show lyz * e * a * (e⁻¹ * lyz⁻¹) = lyz * (e * a * e⁻¹) * lyz⁻¹ by group]
        exact hinv _ (hw a ha)
      have h2 : (lyz * e) * (e * a * e⁻¹) * (lyz * e)⁻¹ = a⁻¹ := by
        rw [mul_inv_rev lyz e,
          show lyz * e * (e * a * e⁻¹) * (e⁻¹ * lyz⁻¹) =
            lyz * (e * (e * a * e⁻¹) * e⁻¹) * lyz⁻¹ by group, hwa]
        exact hinv a ha
      have hc := hAcomm a ha _ (A.inv_mem (hw a ha))
      have hX : (lyz * e) * (a * (e * a * e⁻¹)⁻¹) * (lyz * e)⁻¹ = a * (e * a * e⁻¹)⁻¹ :=
        calc (lyz * e) * (a * (e * a * e⁻¹)⁻¹) * (lyz * e)⁻¹
            = ((lyz * e) * a * (lyz * e)⁻¹) *
                ((lyz * e) * (e * a * e⁻¹) * (lyz * e)⁻¹)⁻¹ := by group
          _ = (e * a * e⁻¹)⁻¹ * (a⁻¹)⁻¹ := by rw [h1, h2]
          _ = (e * a * e⁻¹)⁻¹ * a := by rw [inv_inv]
          _ = a * (e * a * e⁻¹)⁻¹ := hc.eq.symm
      have hconj : (lyz * e) * (a * (e * a * e⁻¹)⁻¹) ^ 3 * (lyz * e)⁻¹ =
          (a * (e * a * e⁻¹)⁻¹) ^ 3 := by
        rw [← conj_pow, hX]
      calc (a * (e * a * e⁻¹)⁻¹) ^ 3 * (lyz * e)
          = (lyz * e) * (a * (e * a * e⁻¹)⁻¹) ^ 3 * (lyz * e)⁻¹ * (lyz * e) := by rw [hconj]
        _ = (lyz * e) * (a * (e * a * e⁻¹)⁻¹) ^ 3 := by group
    have key : ∀ {G : Type} [Group G] (a w : G), a * w = w * a → a ^ 5 = 1 →
        (a * w) ^ 3 * (a * w⁻¹) ^ 3 = a := by
      intro G _ a w hc ha5
      have hc' : Commute a w := hc
      rw [hc'.mul_pow, hc'.inv_right.mul_pow, inv_pow]
      have hc3 : Commute (w ^ 3) (a ^ 3) := hc'.symm.pow_pow 3 3
      calc a ^ 3 * w ^ 3 * (a ^ 3 * (w ^ 3)⁻¹) = a ^ 3 * (w ^ 3 * a ^ 3) * (w ^ 3)⁻¹ := by group
        _ = a ^ 3 * (a ^ 3 * w ^ 3) * (w ^ 3)⁻¹ := by rw [hc3.eq]
        _ = a ^ 5 * a := by group
        _ = a := by rw [ha5, one_mul]
    have hid : ∀ a ∈ A, (a * (e * a * e⁻¹)) ^ 3 * (a * (e * a * e⁻¹)⁻¹) ^ 3 = a := by
      intro a ha
      have hc : a * (e * a * e⁻¹) = (e * a * e⁻¹) * a := (hAcomm a ha _ (hw a ha)).eq
      have ha5 : a ^ 5 = 1 := hA.2 a ha
      have h := key (G := ↥J) a (e * a * e⁻¹) (by exact hc) (by exact ha5)
      exact h
    let f : ↥A → ↥(A ⊓ centralizer {e}) × ↥(A ⊓ centralizer {lyz * e}) := fun a =>
      (⟨_, hm1 a a.2⟩, ⟨_, hm2 a a.2⟩)
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hab
      apply Subtype.ext
      rw [← hid a a.2, ← hid b b.2, hab.1, hab.2]
    have hA25 : Nat.card ↥A ≤ 25 := by
      have h := Nat.card_le_card_of_injective f hf
      rw [Nat.card_prod] at h
      calc Nat.card ↥A ≤ _ := h
        _ ≤ 5 * 5 := Nat.mul_le_mul hc1 hc2
    have hn2 : n ≤ 2 := by
      rw [hn] at hA25
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (hA25.trans (by norm_num) : 5 ^ n ≤ 5 ^ 2)
    interval_cases n <;> rw [Matrix.card_GL_field] at h256 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h256
  ·
    have hfac : (51765179004000000 : ℕ) = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 := by
      norm_num
    have hdvdJ : p ^ n ∣ 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 := by
      rw [← hfac, ← card_J, ← hn]
      exact Subgroup.card_subgroup_dvd_card A
    have hpJ := (dvd_pow_self p hn0).trans hdvdJ
    have hpq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
      (Nat.prime_dvd_prime_iff_eq hp hq).1 h
    have hp' : p = 7 ∨ p = 11 ∨ p = 31 ∨ p = 37 ∨ p = 67 := by
      rcases (Nat.Prime.dvd_mul hp).1 hpJ with h | h67
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h37
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h31
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h11
            · rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
              · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
                · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
                  · have := hpq 2 Nat.prime_two (hp.dvd_of_dvd_pow h2)
                    omega
                  · have := hpq 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)
                    omega
                · have := hpq 5 (by norm_num) (hp.dvd_of_dvd_pow h5)
                  omega
              · exact Or.inl (hpq 7 (by norm_num) h7)
            · exact Or.inr (Or.inl (hpq 11 (by norm_num) h11))
          · exact Or.inr (Or.inr (Or.inl (hpq 31 (by norm_num) h31)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hpq 37 (by norm_num) h37))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hpq 67 (by norm_num) h67))))
    have hn1 : n = 1 := by
      by_contra hn1
      have h2 : p ^ 2 ∣ 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 :=
        (pow_dvd_pow p (by omega)).trans hdvdJ
      rcases hp' with rfl | rfl | rfl | rfl | rfl <;> norm_num at h2
    subst hn1
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;> rw [Matrix.card_GL_field] at h256 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h256

theorem k105SporAt_Ly : K105SporAt .Ly := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowTwoOf lyS ⊤ := ⟨le_top, lySylow.isPGroup', by
    change ¬ 2 ∣ lyS.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact lySylow.not_dvd_index⟩
  have hzc : zS ∈ center ↥lyS := by
    rw [center_lyS]
    exact Subgroup.mem_zpowers _
  have hzcent : lyz ∈ centralizer (lyS : Set J) := Subgroup.mem_centralizer_iff.2 fun s hs => by
    have h := Subgroup.mem_center_iff.1 hzc ⟨s, hs⟩
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  have hSC : lyS ≤ centralizer {lyz} := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzcent s hs)
  have hz2 : orderOf lyz = 2 := (Subgroup.orderOf_coe zS).trans orderOf_zS
  have hz : lyz ∈ CFSG.Open.quasithinOmegaOneCenter lyS := by
    unfold CFSG.Open.quasithinOmegaOneCenter
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨lyz_mem_lyS, hzcent⟩, ?_⟩
    rw [← hz2]
    exact pow_orderOf_eq_one lyz
  have hzQ : lyz ∈ lyQ := by
    have h6 : sE 6 ∈ lyE1 := ((lists_eaSub e16a_mem).2 6 (by norm_num)).1 (by decide)
    rw [← zS_eq] at h6
    rw [lyQ_eq]
    exact ⟨zS, Subgroup.mem_sup_left h6, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : Subgroup J, V = (center ↥lyQ).map lyQ.subtype := ⟨_, rfl⟩
  have hzV : lyz ∈ V := by
    rw [hVdef]
    refine ⟨⟨lyz, hzQ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro q
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
    have h := Subgroup.mem_centralizer_iff.1 hzcent q (lyQ_le q.2)
    exact h
  have hV4 : Nat.card V ≤ 4 := by
    have h4 : Nat.card V = 4 := by
      rw [hVdef, Subgroup.card_map_of_injective lyQ.subtype_injective,
        isKleinFour_center_lyQ.card_four]
    exact h4.le
  have hNV : normalizer (lyQ : Set J) ≤ normalizer (V : Set J) := by
    have key : ∀ g ∈ normalizer (lyQ : Set J), ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
      intro g hg v hv
      rw [hVdef] at hv ⊢
      obtain ⟨c, hc, rfl⟩ := hv
      rw [Subgroup.coe_subtype]
      have hgc : g * (c : J) * g⁻¹ ∈ lyQ := (Subgroup.mem_normalizer_iff.1 hg c).1 c.2
      have hc' : (⟨g * (c : J) * g⁻¹, hgc⟩ : ↥lyQ) ∈ center ↥lyQ := by
        rw [Subgroup.mem_center_iff]
        intro q
        rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
        have hq' : g⁻¹ * (q : J) * g ∈ lyQ := by
          refine (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * q * g)).2 ?_
          have e : g * (g⁻¹ * (q : J) * g) * g⁻¹ = q := by group
          rw [e]
          exact q.2
        have hcq : (g⁻¹ * (q : J) * g) * (c : J) = (c : J) * (g⁻¹ * (q : J) * g) := by
          have h := Subgroup.mem_center_iff.1 hc ⟨_, hq'⟩
          rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h
          exact h
        show (q : J) * (g * (c : J) * g⁻¹) = (g * (c : J) * g⁻¹) * q
        calc (q : J) * (g * (c : J) * g⁻¹) = g * ((g⁻¹ * (q : J) * g) * (c : J)) * g⁻¹ := by
              group
          _ = g * ((c : J) * (g⁻¹ * (q : J) * g)) * g⁻¹ := by rw [hcq]
          _ = (g * (c : J) * g⁻¹) * q := by group
      have hmem := Subgroup.mem_map_of_mem lyQ.subtype hc'
      rw [Subgroup.coe_subtype] at hmem
      exact hmem
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key g hg h, fun hh => ?_⟩
    have h' := key g⁻¹ (inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h'
  have hJ : K105In (normalizer (CFSG.Quasithin.thompsonJ lyS : Set J)) lyS := by
    rw [ly_thompsonJ_eq]
    exact (k105In_normalizer_of_card_le_four hS hSC hzV hV4 ly_k105In_centralizer).mono hNV
  exact k105SporAt_of_k105In hS (k105In_top_of_thompson hS hz ly_k105In_centralizer hJ ly_oddLocal)
    lyEquivJ

end Five

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
