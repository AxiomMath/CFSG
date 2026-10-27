module

public import CFSG.Quasithin.H13.L32A706b
public import CFSG.Quasithin.H13.L32ATJ1b
public import CFSG.Quasithin.H13.L32A706a
public import CFSG.Quasithin.H13.L32ASk7
public import CFSG.Quasithin.H13.L32ASk8

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

namespace Setting147

variable {T L V H : Subgroup G}

theorem normalizer_le_M (S : Setting147 G T L V H) (h1332 : Stmt13_3_2) {N : Subgroup G}
    (hN : N ≠ ⊥) (h2 : IsPGroup 2 N) (hLT : L ⊔ T ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨N, hN, h2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (N : Set G)))
  have hL13 := h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful
  have hMeq := hL13.2.1.2.2.2 M' hM' (hLT.trans hle)
  rw [← hMeq]
  exact hle

theorem false_of_shape (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {Y : Subgroup G} (hYH : Y ≤ H) (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (hYlt : pCoreOf 2 Y < Y) (hYrel : (pCoreOf 2 Y).relIndex Y = p)
    (hYM : Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (hinv : ∀ t ∈ T, t * t ∈ pCoreOf 2 H → ∀ l ∈ l1 T L V, t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 H) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have hTH : T ≤ H := TH' S
  set Q := pCoreOf 2 (L ⊔ T)
  have hQT : Q ≤ T := pCoreOf_le_of_le S.hyp le_sup_right
  have hR1 : ∀ t ∈ T, t * t = 1 → t ∈ pCoreOf 2 (l1 T L V ⊔ T) := fun t ht ht2 =>
    mem_R1_of_involution S h1222 h1332 h1334 hHL hinv ht ht2
  have hEQ : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → A ≤ Q := fun A hAT hA a ha =>
    mem_Q_of_involution S h1222 h1332 h1334 hR1 (hAT ha) (by rw [← pow_two]; exact hA.2 a ha)
  have hJQ : thompsonJ T ≤ Q := iSup₂_le fun A hA => hEQ A hA.1 hA.2.1
  have hJ1Q : thompsonJi T 1 ≤ Q := iSup₂_le fun A hA => hEQ A hA.1 hA.2.1
  have hVe : IsElemAbelian 2 V := ⟨inferInstance, fun v hv => S14.sq_V hv⟩
  have hrank : 3 ≤ CFSG.Open.pRank 2 T := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have h := (isMaxElemAbelian_iff_corank_zero.mp hA₀).2.2
    rw [pow_zero, mul_one] at h
    have h8 : Nat.card V ≤ Nat.card A₀ := hA₀.2.2 V S14.VT hVe
    rw [S14.card_V, h] at h8
    by_contra hlt
    push Not at hlt
    have : 2 ^ CFSG.Open.pRank 2 T ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hJ : thompsonJ T = thompsonJ Q := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega) (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJQ) hQT
  have hJ1 : thompsonJi T 1 = thompsonJi Q 1 := thompsonJi_eq_of_le (by omega) hJ1Q hQT
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 (L ⊔ T)
  have hJne : thompsonJ T ≠ ⊥ := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    intro hb
    have hA₀J : A₀ ≤ thompsonJ T := le_iSup₂_of_le A₀ hA₀ le_rfl
    have h8 : Nat.card V ≤ Nat.card A₀ := hA₀.2.2 V S14.VT hVe
    rw [le_bot_iff.mp (hA₀J.trans hb.le), Subgroup.card_bot, S14.card_V] at h8
    omega
  have hNJ : Subgroup.normalizer (thompsonJ T : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_le_M S h1332 hJne ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le hJQ)
      (by rw [hJ]; exact hLTQ.trans (normalizer_le_normalizer_thompsonJ Q))
  have hE : omegaOneCenterOf (thompsonJi T 1) =
      omegaOneOf (T ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G)) :=
    (omegaOneCenterOf_thompsonJi_le (S := T) (le_refl 1) (by omega)).2.symm
  obtain ⟨z, -, -, hz, hz1, -, -, -, -⟩ := S14.exists_basis
  have hzT : z ∈ T := S14.VT (Subgroup.mem_inf.mp hz).1
  have hzE : z ∈ omegaOneCenterOf (thompsonJi T 1) := by
    rw [hE]
    refine Subgroup.subset_closure ⟨⟨hzT, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩, ?_⟩
    · have hjT : j ∈ T := hJ1Q.trans hQT hj
      have h1 := fix_z_of_N S14 hz hz1 (S.hz.2.1 (hTH hjT))
      calc j * z = (j * z * j⁻¹) * j := by group
        _ = z * j := by rw [h1]
    · rw [pow_two]
      exact S14.mul_self_V (Subgroup.mem_inf.mp hz).1
  have hEne : omegaOneCenterOf (thompsonJi T 1) ≠ ⊥ := fun hb => hz1 (by
    rw [hb] at hzE
    exact (Subgroup.mem_bot).mp hzE)
  have hET : omegaOneCenterOf (thompsonJi T 1) ≤ T := by
    rw [hE]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1.1
  have hNE : Subgroup.normalizer (omegaOneCenterOf (thompsonJi T 1) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    refine normalizer_le_M S h1332 hEne (S.hyp.fsu.sylow.1.to_le hET) ?_
    rw [hJ1]
    exact hLTQ.trans (normalizer_le_normalizer_of_map_mulEquiv
      (F := fun X => omegaOneCenterOf (thompsonJi X 1))
      (fun φ X => by
        show (omegaOneCenterOf (thompsonJi X 1)).map φ.toMonoidHom =
          omegaOneCenterOf (thompsonJi (X.map φ.toMonoidHom) 1)
        rw [omegaOneCenterOf_map_mulEquiv, thompsonJi_map_mulEquiv151]) Q)
  have hXH : Y ⊔ T ≤ H := sup_le hYH hTH
  have hT := S.hyp.fsu.sylow
  have hchar : CharTwo H := by
    refine CFSG.Quasithin.charTwo_of_inH S.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2) ⟨?_, S.hz.1.2⟩
    rw [IsPGroup.toSylow_coe]
    exact hTH
  have hUT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp hTH
  have hcharX : CharTwo (Y ⊔ T) := by
    have hUX : pCoreOf 2 H ≤ pCoreOf 2 (Y ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 (hUT.trans le_sup_right)
        (fun x hx => le_normalizer_pCoreOf 2 H (hXH hx)) (pCoreOf_isPGroup 2 H)
    intro x hx
    refine hUX (hchar ⟨hXH hx.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩)
    exact Subgroup.mem_centralizer_iff.mp hx.2 u (hUX hu)
  rcases thompson_J1_prime hp hp5 le_sup_left (hXH.trans hHY) hYrel rfl
      (isSylowTwoOf_of_le151 hT le_sup_right) hcharX with h | h
  · exact hYlt.ne (by rw [← hYM]; exact inf_eq_left.mpr ((le_sup_left.trans h).trans hNJ))
  · exact hYlt.ne (by rw [← hYM]; exact inf_eq_left.mpr ((le_sup_left.trans h).trans hNE))

end Setting147

theorem lemma14_7_6_of (h520 : Lemma14_5_20) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hShape : Input1476Shape) : Lemma14_7_6 := by
  intro G _ _ T L V H S
  suffices h : ∀ n : ℕ, ∀ H : Subgroup G, Nat.card H = n → Setting147 G T L V H →
      IsPGroup 3 ↥(CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)) from h _ H rfl S
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn S
    refine isPGroup_fitting_of_pCore fun p hp hp3 => ?_
    by_contra hO
    rcases (by have := hp.two_le; omega : p = 2 ∨ p = 4 ∨ 5 ≤ p) with rfl | rfl | hp5
    · exact hO CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
    · exact absurd hp (by norm_num)
    · obtain ⟨Y, hYO, hYH, hHY, hYp, hYlt, hYM, hmin, hS₀, hO₀⟩ :=
        Setting147.reduce h520 h1222 h1332 h1334 S hp hp5 hO
      rcases lt_or_eq_of_le (sup_le hYH S.hz.1.1 : Y ⊔ (l1 T L V ⊔ T) ≤ H) with hlt | heq
      ·
        have h3 := ih _ (by rw [← hn]; exact Subgroup.card_lt_of_lt hlt) _ rfl hS₀
        have : Fact p.Prime := ⟨hp⟩
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hP3 := h3.to_le (CFSG.pCore_le_fitting _ p)
        exact hO₀ (disjoint_self.mp
          (IsPGroup.disjoint_of_ne p 3 hp3 _ _ CFSG.pCore_isPGroup hP3))
      ·
        obtain ⟨hrel, hHL, hinv⟩ :=
          hShape G T L V H S p hp hp5 Y hYO hYH hHY hYp hYlt hYM heq.symm hmin
        exact Setting147.false_of_shape h1222 h1332 h1334 S hp hp5 hYH hHY hYlt hrel hYM hHL
          hinv

end CFSG.Quasithin.H13.L32A
