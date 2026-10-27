module

public import CFSG.Quasithin.H13.U3G2Pair
public import CFSG.Quasithin.H13.U3X10
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem inf_centralizer_cjSub {K Y : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) :
    K ⊓ centralizer (cjSub g Y : Set G) = cjSub g (K ⊓ centralizer (Y : Set G)) := by
  ext y
  rw [mem_inf, mem_cjSub, mem_inf]
  constructor
  · rintro ⟨hyK, hyC⟩
    refine ⟨?_, mem_centralizer_iff.2 fun v hv => ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem hg) y).1 hyK
      simpa using this
    · have hv' : g * v * g⁻¹ ∈ cjSub g Y := mem_cjSub.2 (by simpa [mul_assoc] using hv)
      have h1 := mem_centralizer_iff.1 hyC _ hv'
      calc v * (g⁻¹ * y * g) = g⁻¹ * ((g * v * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * v * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * y * g * v := by group
  · rintro ⟨hyK, hyC⟩
    refine ⟨?_, mem_centralizer_iff.2 fun w hw => ?_⟩
    · have := (mem_normalizer_iff.1 hg _).1 hyK
      simpa [mul_assoc] using this
    · have h1 := mem_centralizer_iff.1 hyC _ (mem_cjSub.1 hw)
      have h2 : g⁻¹ * (w * y) * g = g⁻¹ * (y * w) * g := by
        calc g⁻¹ * (w * y) * g = (g⁻¹ * w * g) * (g⁻¹ * y * g) := by group
          _ = (g⁻¹ * y * g) * (g⁻¹ * w * g) := h1
          _ = g⁻¹ * (y * w) * g := by group
      exact mul_left_cancel (mul_right_cancel h2)

theorem cjSub_mul (a b : G) (X : Subgroup G) : cjSub (a * b) X = cjSub a (cjSub b X) := by
  ext y
  rw [mem_cjSub, mem_cjSub, mem_cjSub]
  have e : (a * b)⁻¹ * y * (a * b) = b⁻¹ * (a⁻¹ * y * a) * b := by group
  rw [e]

theorem cjSub_injective (g : G) {X Y : Subgroup G} (h : cjSub g X = cjSub g Y) : X = Y := by
  have h1 := congrArg (cjSub g⁻¹) h
  rwa [cjSub_inv_cjSub, cjSub_inv_cjSub] at h1

theorem sqSub_cjSub (g : G) (D : Subgroup G) : C5.sqSub (cjSub g D) = cjSub g (C5.sqSub D) := by
  apply le_antisymm
  · refine C5.sqSub_le_of_forall fun d hd => mem_cjSub.2 ?_
    have e : g⁻¹ * d ^ 2 * g = (g⁻¹ * d * g) ^ 2 := by
      rw [pow_two, pow_two]
      group
    rw [e]
    exact C5.sq_mem_sqSub (mem_cjSub.1 hd)
  · have h : C5.sqSub D ≤ cjSub g⁻¹ (C5.sqSub (cjSub g D)) := by
      refine C5.sqSub_le_of_forall fun d hd => mem_cjSub.2 ?_
      have e : g⁻¹⁻¹ * d ^ 2 * g⁻¹ = (g * d * g⁻¹) ^ 2 := by
        rw [pow_two, pow_two]
        group
      rw [e]
      exact C5.sq_mem_sqSub (mem_cjSub.2 (by simpa [mul_assoc] using hd))
    have := cjSub_mono (g := g) h
    rwa [cjSub_cjSub_inv] at this

theorem relIndex_ne_zero' [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := fun h => by
  have := relIndex_mul_card H K
  rw [h, zero_mul] at this
  exact Nat.card_pos.ne this

theorem relIndex_eq_of_card_eq [Finite G] {H₁ H₂ K : Subgroup G} (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K)
    (hc : Nat.card H₁ = Nat.card H₂) : H₁.relIndex K = H₂.relIndex K := by
  have e₁ := relIndex_mul_card H₁ K
  rw [inf_eq_left.2 h₁, hc] at e₁
  have e₂ := relIndex_mul_card H₂ K
  rw [inf_eq_left.2 h₂] at e₂
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e₁.trans e₂.symm)

theorem relIndex_inf_le_of_le [Finite G] {Q B C : Subgroup G} (hQB : Q ≤ B) :
    (Q ⊓ C).relIndex Q ≤ (B ⊓ C).relIndex B := by
  have e : (B ⊓ C) ⊓ Q = Q ⊓ C := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.2 hQB]
  calc (Q ⊓ C).relIndex Q = ((B ⊓ C) ⊓ Q).relIndex Q := by rw [e]
    _ = (B ⊓ C).relIndex Q := inf_relIndex_right _ _
    _ ≤ (B ⊓ C).relIndex B := relIndex_le_of_le_right hQB (relIndex_ne_zero' _ _)

theorem normalizer_le_of_two [Finite G] {T N Q Q' : Subgroup G} (hT : ¬ 2 ∣ T.index) (hTN : T ≤ N)
    (hTQ : T ≤ normalizer (Q : Set G)) (h : ∀ g ∈ N, cjSub g Q = Q ∨ cjSub g Q = Q') :
    N ≤ normalizer (Q : Set G) := by
  by_contra hne
  obtain ⟨g, hgN, hgQ⟩ := IsConcreteLE.not_le_iff_exists.1 hne
  have hgQ' : ¬ cjSub g Q = Q := fun h' => hgQ (B2F.mem_normalizer_iff_cjSub_eq.2 h')
  have hgx : cjSub g Q = Q' := (h g hgN).resolve_left hgQ'
  have hQQ' : Q' ≠ Q := fun h' => hgQ' (hgx.trans h')
  set K := N ⊓ normalizer (Q : Set G) with hK
  have hrel : K.relIndex N = 2 := by
    refine relIndex_eq_two_iff.2 ⟨g, hgN, fun b hb => ?_⟩
    have hbg : b * g ∈ N := mul_mem hb hgN
    rcases h b hb with hbQ | hbQ
    ·
      right
      refine ⟨⟨hb, B2F.mem_normalizer_iff_cjSub_eq.2 hbQ⟩, fun hbgK => ?_⟩
      have h1 : cjSub (b * g) Q = Q := B2F.mem_normalizer_iff_cjSub_eq.1 hbgK.2
      rw [cjSub_mul, hgx] at h1
      exact hQQ' (cjSub_injective b (h1.trans hbQ.symm))
    ·
      left
      refine ⟨⟨hbg, ?_⟩, fun hbK => hQQ' (hbQ.symm.trans
        (B2F.mem_normalizer_iff_cjSub_eq.1 hbK.2))⟩
      show b * g ∈ normalizer (Q : Set G)
      rw [B2F.mem_normalizer_iff_cjSub_eq]
      rcases h (b * g) hbg with h1 | h1
      · exact h1
      · exfalso
        rw [cjSub_mul, hgx] at h1
        exact hQQ' (cjSub_injective b (h1.trans hbQ.symm))
  have hTK : T ≤ K := le_inf hTN hTQ
  have h1 := relIndex_mul_relIndex T K N hTK (inf_le_left : K ≤ N)
  rw [hrel] at h1
  exact hT ((Dvd.intro_left _ h1).trans (relIndex_dvd_index_of_le hTN))

theorem autI_eq_of {Q B K : Subgroup G} (hQ : IsElemAbelian 2 Q) (hKB : K ≤ B)
    (hBN : B ≤ normalizer (Q : Set G)) (h : ∀ b ∈ B, ∃ k ∈ K, k⁻¹ * b ∈ Q) :
    autI hQ K = autI hQ B := by
  refine le_antisymm (autI_mono hQ hKB) fun φ hφ => ?_
  obtain ⟨⟨b, hbN⟩, hbB, rfl⟩ := (mem_autI hQ).1 hφ
  obtain ⟨k, hkK, hkb⟩ := h b hbB
  have hkN : k ∈ normalizer (Q : Set G) := hBN (hKB hkK)
  have h1 : convI hQ (⟨k, hkN⟩⁻¹ * ⟨b, hbN⟩) = 1 :=
    (convI_eq_one_iff hQ _).2 (B2F.le_centralizer_self hQ hkb)
  have h2 : convI hQ ⟨b, hbN⟩ = convI hQ ⟨k, hkN⟩ := by
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  rw [h2]
  exact convI_mem_autI hQ hkK hkN

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem B_le_normalizer_Q
    (S : HullSetting G T L V z) {K : Subgroup G} (hK : K ≤ normalizer (V : Set G)) :
    K ⊓ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G) ≤
      normalizer ((baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) :
        Subgroup G) : Set G) := by
  rintro g ⟨hgK, hgB⟩
  have hgC := mem_normalizer_centralizer_V (hK hgK)
  rw [mem_normalizer_iff]
  intro y
  rw [mem_inf, mem_inf, mem_normalizer_iff.1 hgB y, mem_normalizer_iff.1 hgC y]

theorem Q_facts
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) :
    V ≤ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) ∧
      L ⊔ T ≤ normalizer ((baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) :
        Subgroup G) : Set G) ∧
      normalizer ((baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) : Subgroup G) :
        Set G) ≤ normalizer (L : Set G) := by
  have hVQ : V ≤ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) :=
    le_inf S.V_le_B (B2F.le_centralizer_self (isElemAbelian_of_isElementaryAbelian' V))
  have hQT : baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) ≤ T :=
    inf_le_left.trans S.B_le_T
  have hTQ : T ≤ normalizer ((baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) :
      Subgroup G) : Set G) :=
    fun t ht => S.B_le_normalizer_Q S.hTV ⟨ht, S.T_le_normalizer_B ht⟩
  exact ⟨hVQ, sup_le (S.le_normalizer_of hL hVL hVQ hQT inf_le_right) hTQ,
    S.normalizer_le_of hL hVL hVQ hQT inf_le_right hTQ⟩

theorem exists_D
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) :
    ∃ D : Subgroup G, D ≤ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) ∧
      D ≤ centralizer (cjSub x V : Set G) ∧ Disjoint V D ∧
      Nat.card ↥(baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G)) ≤
        64 * Nat.card D := by
  set B := baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) with hBdef
  set Q := B ⊓ centralizer (V : Set G) with hQdef
  set X := cjSub x V with hXdef
  obtain ⟨hVQ, hLTQ, -⟩ := S.Q_facts hL hVL
  obtain ⟨l, hl, hlN, hlspec⟩ := S.exists_lift oppGL_mem
  have hlQ : l ∈ normalizer (Q : Set G) := hLTQ (mem_sup_left hl)
  set D := (Q ⊓ centralizer (X : Set G)) ⊓ (Q ⊓ centralizer (cjSub l X : Set G)) with hD
  refine ⟨D, inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, ?_, ?_⟩
  · rw [disjoint_def]
    intro v hvV hvD
    have hv3 : v ∈ S.V₃ := by
      rw [← S.inf_centralizer_cjSub_eq hx hxV]
      exact ⟨hvV, hvD.1.2⟩
    set w := l⁻¹ * v * l with hw
    have hwV : w ∈ V := by
      have := (mem_normalizer_iff.1 (inv_mem hlN) v).1 hvV
      simpa [hw] using this
    have hw3 : w ∈ S.V₃ := by
      rw [← S.inf_centralizer_cjSub_eq hx hxV]
      refine ⟨hwV, mem_centralizer_iff.2 fun n hn => ?_⟩
      have hn' : l * n * l⁻¹ ∈ cjSub l X := mem_cjSub.2 (by simpa [mul_assoc] using hn)
      have h1 := mem_centralizer_iff.1 hvD.2.2 _ hn'
      have h2 : l * (n * w) * l⁻¹ = l * (w * n) * l⁻¹ := by
        calc l * (n * w) * l⁻¹ = l * n * l⁻¹ * v := by rw [hw]; group
          _ = v * (l * n * l⁻¹) := h1
          _ = l * (w * n) * l⁻¹ := by rw [hw]; group
      exact mul_left_cancel (mul_right_cancel h2)
    rw [S.V₃_eq_pullSub] at hv3 hw3
    obtain ⟨hvV', hvP⟩ := mem_pullSub.1 hv3
    obtain ⟨hwV', hwP⟩ := mem_pullSub.1 hw3
    have h1 := phi_conj' hlN hlspec hwV'
    have hlw : l * w * l⁻¹ = v := by rw [hw]; group
    rw [show (⟨l * w * l⁻¹, (mem_normalizer_iff.1 hlN w).1 hwV'⟩ : V) = ⟨v, hvV'⟩ from
      Subtype.ext hlw] at h1
    have h0 : S.Φ (Additive.ofMul (⟨w, hwV'⟩ : V)) = 0 :=
      opp_V3sub hwP (h1 ▸ hvP)
    have hw1 : w = 1 := by
      have h2 : S.Φ (Additive.ofMul (⟨w, hwV'⟩ : V)) =
          S.Φ (Additive.ofMul (⟨1, V.one_mem⟩ : V)) := by
        rw [h0]
        exact S.Φ.map_zero.symm
      exact phi_injective' _ _ h2
    rw [← hlw, hw1]
    group
  · have hQB : Q ≤ B := inf_le_left
    have h1 : (Q ⊓ centralizer (X : Set G)).relIndex Q ≤ 8 := by
      refine (relIndex_inf_le_of_le hQB).trans ?_
      rw [relIndex_eq_of_card_eq inf_le_left inf_le_left
        (by rw [inf_centralizer_cjSub hx, card_cjSub] : Nat.card ↥(B ⊓ centralizer (X : Set G)) =
          Nat.card ↥(B ⊓ centralizer (V : Set G)))]
      exact S.card_B_le
    have h2 : (Q ⊓ centralizer (cjSub l X : Set G)).relIndex Q ≤ 8 := by
      rw [relIndex_eq_of_card_eq inf_le_left inf_le_left
        (by rw [inf_centralizer_cjSub hlQ, card_cjSub] :
          Nat.card ↥(Q ⊓ centralizer (cjSub l X : Set G)) =
            Nat.card ↥(Q ⊓ centralizer (X : Set G)))]
      exact h1
    have h3 := relIndex_inf_le (H := Q ⊓ centralizer (X : Set G))
      (K := Q ⊓ centralizer (cjSub l X : Set G)) (L := Q)
    have h4 := relIndex_mul_card D Q
    rw [inf_eq_left.2 (inf_le_left.trans inf_le_left : D ≤ Q)] at h4
    rw [← h4]
    exact Nat.mul_le_mul_right _ (h3.trans (by nlinarith))

theorem sup_eq
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) {D : Subgroup G}
    (hDQ : D ≤ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G))
    (hDX : D ≤ centralizer (cjSub x V : Set G)) (hVD : Disjoint V D)
    (hc : Nat.card ↥(baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G)) ≤
      64 * Nat.card D) :
    V ⊔ D = baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) ∧
      cjSub x V ⊔ D = baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (cjSub x V : Set G) := by
  obtain ⟨hVQ, -, -⟩ := S.Q_facts hL hVL
  have hXab := isElemAbelian_cjSub (g := x) (isElemAbelian_of_isElementaryAbelian' V)
  have hDN : D ≤ normalizer (V : Set G) :=
    C5.le_normalizer_of_commute fun d hd v hv => (mem_centralizer_iff.1 (hDQ hd).2 v hv).symm
  have hDNX : D ≤ normalizer (cjSub x V : Set G) :=
    C5.le_normalizer_of_commute fun d hd v hv => (mem_centralizer_iff.1 (hDX hd) v hv).symm
  have h1 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V D hDN hVD
  rw [S.hV64] at h1
  refine ⟨Subgroup.eq_of_le_of_card_ge (sup_le hVQ hDQ) (by rw [h1]; exact hc), ?_⟩
  have hXD : Disjoint (cjSub x V) D := by
    rw [disjoint_def]
    intro y hyX hyD
    have hyV3 : y ∈ S.V₃ := by
      rw [← S.cjSub_inf_centralizer_eq hx hxV]
      exact ⟨hyX, (hDQ hyD).2⟩
    exact disjoint_def.1 hVD (S.le3 hyV3) hyD
  have h2 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (cjSub x V) D hDNX
    hXD
  rw [card_cjSub, S.hV64] at h2
  refine Subgroup.eq_of_le_of_card_ge (sup_le (le_inf (cjSub_le hx S.V_le_B)
    (B2F.le_centralizer_self hXab)) (le_inf ((hDQ.trans inf_le_left)) hDX)) ?_
  rw [h2, inf_centralizer_cjSub hx, card_cjSub]
  exact hc

theorem isElemAbelian_Q
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) :
    IsElemAbelian 2 (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G)) := by
  set Q := baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) with hQdef
  obtain ⟨D, hDQ, hDX, hVD, hc⟩ := S.exists_D hL hVL hx hxV
  obtain ⟨h1, h2⟩ := S.sup_eq hL hVL hx hxV hDQ hDX hVD hc
  obtain ⟨-, hLTQ, -⟩ := S.Q_facts hL hVL
  have hV2 : ∀ u ∈ V, u ^ 2 = 1 := (isElemAbelian_of_isElementaryAbelian' V).2
  have hW2 : ∀ u ∈ cjSub x V, u ^ 2 = 1 :=
    (isElemAbelian_cjSub (g := x) (isElemAbelian_of_isElementaryAbelian' V)).2
  have hcV : ∀ u ∈ V, ∀ a ∈ D, u * a = a * u := fun u hu a ha =>
    mem_centralizer_iff.1 (hDQ ha).2 u hu
  have hcW : ∀ u ∈ cjSub x V, ∀ a ∈ D, u * a = a * u := fun u hu a ha =>
    mem_centralizer_iff.1 (hDX ha) u hu
  have e1 : C5.sqSub Q = C5.sqSub D := by
    rw [hQdef, ← h1]
    exact C5.sqSub_sup_eq hV2 hcV
  have e2 : C5.sqSub (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓
      centralizer (cjSub x V : Set G)) = C5.sqSub D := by
    rw [← h2]
    exact C5.sqSub_sup_eq hW2 hcW
  have e3 : cjSub x (C5.sqSub Q) = C5.sqSub Q := by
    rw [← sqSub_cjSub, hQdef, ← inf_centralizer_cjSub hx, e2, ← hQdef, e1]
  have hxN : x ∈ normalizer (C5.sqSub Q : Set G) := B2F.mem_normalizer_iff_cjSub_eq.2 e3
  have hsq : C5.sqSub Q = ⊥ := by
    by_contra hne
    have hLTsq : L ⊔ T ≤ normalizer (C5.sqSub Q : Set G) := fun g hg =>
      B2F.mem_normalizer_iff_cjSub_eq.2 (by
        rw [← sqSub_cjSub, B2F.mem_normalizer_iff_cjSub_eq.1 (hLTQ hg)])
    have hle := normalizer_le_of_isUniqueM S.uniqueM
      (S.hH.sylow.1.to_le (C5.sqSub_le_self.trans (inf_le_left.trans S.B_le_T))) hne hLTsq
    have hxV' := S.normalizer_L_le hL hVL (hle hxN)
    apply hxV
    rw [B2F.mem_normalizer_iff_cjSub_eq.1 hxV']
    exact B2F.le_centralizer_self (isElemAbelian_of_isElementaryAbelian' V)
  have hq2 := C5.sqSub_eq_bot_iff.1 hsq
  exact ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (C5.comm_of_sq_eq_one hq2 a a.2 b b.2),
    hq2⟩

theorem isMaxElemAbelian_Q
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) :
    IsMaxElemAbelian (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)))
      (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G)) := by
  have hQ := S.isElemAbelian_Q hL hVL hx hxV
  obtain ⟨hVQ, -, -⟩ := S.Q_facts hL hVL
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)))
  have hAT : A ≤ T := hA.1.trans S.B_le_T
  have hV := isElemAbelian_of_isElementaryAbelian' V
  have heq : Nat.card V = (A ⊓ centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ centralizer (A : Set G)) :=
    le_antisymm (card_le_relIndex_mul_card hV S.V_le_B hA)
      (by rw [S.hV64]; exact S.card_mul_card_le hAT hA.2.1)
  have hsup := (B24_three hV S.V_le_B hA heq).1
  have hle : (A ⊓ centralizer (V : Set G)) ⊔ V ≤
      baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) :=
    sup_le (inf_le_inf_right _ hA.1) hVQ
  exact ⟨inf_le_left, hQ, fun E hEB hE => (hsup.2.2 E hEB hE).trans (card_le_of_le hle)⟩

theorem exists_inv_mul_mem
    (S : HullSetting G T L V z) {K : Subgroup G}
    (hKB : K ≤ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)))
    (hK : ∀ e ∈ S0L, (∀ w ∈ V3sub, e w = w) → e ∈ S.imgL K) :
    ∀ b ∈ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)), ∃ k ∈ K,
      k⁻¹ * b ∈ baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) := by
  intro b hb
  have hbN : b ∈ normalizer (V : Set G) := S.hTV (S.B_le_T hb)
  have he := S.glLin_rho_mem_imgL hb hbN
  obtain ⟨k, hkN, hkK, hk⟩ := S.mem_imgL.1 (hK _ (S.imgL_le_S0L S.B_le_T he)
    (S.imgL_B_fix _ he))
  refine ⟨k, hkK, mem_inf.2 ⟨mul_mem (inv_mem (hKB hkK)) hb, ?_⟩⟩
  have hρ : S.rho (⟨k, hkN⟩⁻¹ * ⟨b, hbN⟩) = 1 := by
    rw [map_mul, map_inv, glLin.injective hk, inv_mul_cancel]
  exact (mem_centralizer_V_iff (mul_mem (inv_mem hkN) hbN) (S.rho_spec _)).2 hρ

theorem mem_A_B
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T))) A) :
    A = baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) ∨
      A = baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (cjSub x V : Set G) := by
  set B := baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) with hBdef
  set Q := B ⊓ centralizer (V : Set G) with hQdef
  set X := cjSub x V with hXdef
  have hV := isElemAbelian_of_isElementaryAbelian' V
  have hXab : IsElemAbelian 2 X := isElemAbelian_cjSub hV
  obtain ⟨hVQ, -, -⟩ := S.Q_facts hL hVL
  have hQ := S.isElemAbelian_Q hL hVL hx hxV
  have hQmax := S.isMaxElemAbelian_Q hL hVL hx hxV
  have hAT : A ≤ T := hA.1.trans S.B_le_T
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans S.hTV
  by_cases hAC : A ≤ centralizer (V : Set G)
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge (le_inf hA.1 hAC) (hA.2.2 Q inf_le_left hQ))
  right
  have hA1 : IsA1 (S.imgL A) := by
    refine isA1_of_fix (S.imgL_le_S0L hAT) (S.isElementaryAbelian_imgL hA.2.1) ?_ ?_ ?_
    · rw [S.card_imgL hAN, ← S.card_inf_centralizer hAN]
      exact le_antisymm (S.card_mul_card_le hAT hA.2.1)
        (S.hV64 ▸ card_le_relIndex_mul_card hV S.V_le_B hA)
    · exact fun h => hAC ((S.imgL_eq_bot_iff hAN).1 h)
    · exact fun e he => S.imgL_B_fix e (S.imgL_mono hA.1 he)
  have hX1 := S.isA1_imgL hx hxV
  obtain ⟨D, hDQ, hDX, hVD, hc⟩ := S.exists_D hL hVL hx hxV
  obtain ⟨h1, h2⟩ := S.sup_eq hL hVL hx hxV hDQ hDX hVD hc
  have hXQx : X ≤ B ⊓ centralizer (X : Set G) :=
    le_inf (cjSub_le hx S.V_le_B) (B2F.le_centralizer_self hXab)
  have hQxmax : IsMaxElemAbelian B (B ⊓ centralizer (X : Set G)) := by
    rw [inf_centralizer_cjSub hx]
    exact isMaxElemAbelian_cjSub hx hQmax
  have hBQ : B ≤ normalizer (Q : Set G) := fun b hb =>
    S.B_le_normalizer_Q (S.B_le_T.trans S.hTV) ⟨hb, le_normalizer hb⟩
  have hC : B ⊓ centralizer (Q : Set G) = Q :=
    le_antisymm (fun b hb => ⟨hb.1, centralizer_le hVQ hb.2⟩)
      (le_inf inf_le_left (B2F.le_centralizer_self hQ))
  obtain ⟨u, huN, huX, hu⟩ := S.mem_imgL.1 hX1.mem_21
  have hcent : Q ⊓ centralizer ((B ⊓ centralizer (X : Set G) : Subgroup G) : Set G) =
      Q ⊓ centralizer ({u} : Set G) := by
    refine le_antisymm (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.2
      (hXQx huX)))) ?_
    rintro q ⟨hqQ, hqu⟩
    refine ⟨hqQ, ?_⟩
    have hqQ' : q ∈ ((V ⊔ D : Subgroup G) : Set G) := by rw [h1]; exact hqQ
    rw [coe_mul_of_left_le_normalizer_right V D
      (C5.le_normalizer_of_commute fun v hv d hd => mem_centralizer_iff.1 (hDQ hd).2 v hv)]
      at hqQ'
    obtain ⟨v, hv, d, hd, rfl⟩ := hqQ'
    have hdu : u * d = d * u := mem_centralizer_iff.1 (hDX hd) u huX
    have hqu' : u * (v * d) = v * d * u := (mem_centralizer_iff.1 hqu u rfl)
    have hvu : u * v = v * u := by
      have : u * v * d = v * u * d := by
        calc u * v * d = u * (v * d) := by group
          _ = v * d * u := hqu'
          _ = v * (u * d) := by rw [hdu]; group
          _ = v * u * d := by group
      exact mul_right_cancel this
    have hvX : v ∈ centralizer (X : Set G) := by
      have h3 := (S.comm_iff_fix huN hv).1 hvu
      rw [hu, IsA1.fix_21_iff] at h3
      have hv3 : v ∈ S.V₃ := by
        rw [S.V₃_eq_pullSub]
        exact mem_pullSub.2 ⟨hv, h3⟩
      rw [← S.inf_centralizer_cjSub_eq hx hxV] at hv3
      exact hv3.2
    rw [← h2]
    have hsub : X ⊔ D ≤ centralizer ({v * d} : Set G) := by
      refine sup_le (fun w hw => mem_centralizer_singleton_iff.2 ?_)
        (fun d' hd' => mem_centralizer_singleton_iff.2 ?_)
      · have hwv : w * v = v * w := mem_centralizer_iff.1 hvX w hw
        have hwd : w * d = d * w := mem_centralizer_iff.1 (hDX hd) w hw
        calc w * (v * d) = w * v * d := by group
          _ = v * w * d := by rw [hwv]
          _ = v * (w * d) := by group
          _ = v * (d * w) := by rw [hwd]
          _ = v * d * w := by group
      · have hvd' : v * d' = d' * v := mem_centralizer_iff.1 (hDQ hd').2 v hv
        have hdd' : d * d' = d' * d := B2F.isElemAbelian_comm hQ (hDQ hd) (hDQ hd')
        calc d' * (v * d) = d' * v * d := by group
          _ = v * d' * d := by rw [← hvd']
          _ = v * (d' * d) := by group
          _ = v * (d * d') := by rw [← hdd']
          _ = v * d * d' := by group
    exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hsub hy)
  have hAB : autI hQ (B ⊓ centralizer (X : Set G)) = autI hQ A := by
    rw [autI_eq_of hQ inf_le_left hBQ (S.exists_inv_mul_mem inf_le_left fun e he hfix =>
        S.imgL_mono hXQx (hX1.mem_of_fix he hfix)),
      autI_eq_of hQ hA.1 hBQ (S.exists_inv_mul_mem hA.1 fun e he hfix => hA1.mem_of_fix he hfix)]
  exact B2_21 hQ inf_le_left hBQ hC hQxmax (hXQx huX) hcent hA hAB

theorem false_of_x
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) {x : G}
    (hx : x ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G))
    (hxV : ¬ cjSub x V ≤ centralizer (V : Set G)) : False := by
  obtain ⟨hVQ, hLTQ, -⟩ := S.Q_facts hL hVL
  have hQmax := S.isMaxElemAbelian_Q hL hVL hx hxV
  have hle := normalizer_le_of_two S.hH.sylow.2 S.T_le_normalizer_B (le_sup_right.trans hLTQ)
    fun g hg => S.mem_A_B hL hVL hx hxV (isMaxElemAbelian_cjSub hg hQmax)
  apply hxV
  calc cjSub x V ≤ cjSub x (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G)) :=
        cjSub_mono hVQ
    _ = baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) ⊓ centralizer (V : Set G) :=
        B2F.mem_normalizer_iff_cjSub_eq.1 (hle hx)
    _ ≤ centralizer (V : Set G) := inf_le_right

theorem normalizer_B_le
    (S : HullSetting G T L V z) (hL : IsShort2 L) (hVL : ⁅V, L⁆ = V) :
    normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G) ≤ normalizer (L : Set G) := by
  by_cases h : ∀ g ∈ normalizer (baum (pCoreOf 2 (L₁Of L S.V₁ ⊔ T)) : Set G),
      cjSub g V ≤ centralizer (V : Set G)
  · exact S.normalizer_B_le_of_comm hL hVL h
  · push Not at h
    obtain ⟨x, hx, hxV⟩ := h
    exact (S.false_of_x hL hVL hx hxV).elim

end HullSetting

theorem stmt13_3_10G2_of
    (h1332 : Stmt13_3_2) : Stmt13_3_10G2 := by
  intro G _ _ T L V Lp hH hV hZV hLp hU3 hB
  obtain ⟨z, hF⟩ := u3_frame_of_irrPlus h1332 hH hU3 hV
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  let S : HullSetting G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  subst hLp
  rw [S.fsuV1_eq_V₁]
  exact S.normalizer_B_le hB.1 hV.2.2.2.1

theorem stmt13_3_10_of_c137
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h1334 : A6.Stmt13_3_4)
    (hC137 : C137Statement) (h13227 : Stmt13_2_2_7) : Stmt13_3_10 :=
  stmt13_3_10_of h1332 h1222 h1334 hC137 h13227 (stmt13_3_10G2_of h1332)

end CFSG.Quasithin.H13.U3
