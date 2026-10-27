module

public import CFSG.Quasithin.H13.L32NItems144CTL6
public import CFSG.Quasithin.Vol2.Ch1Lem125
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_map_conj (X : Subgroup G) (h : G) :
    Nat.card ↥(X.map (MulAut.conj h).toMonoidHom) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj h).injective

omit [Finite G] in
theorem relIndex_sup_eq_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem card_inf_R {σ h : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hhH : h ∈ l32nH T V)
    (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V)) (hσT : σ ∈ T) :
    Nat.card ↥(L.map (MulAut.conj h).toMonoidHom ⊓
      (pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ)) = 2 ^ 6 := by
  have hL₀c : Nat.card ↥(L.map (MulAut.conj h).toMonoidHom) = 1344 := by
    rw [card_map_conj, S.cardL]
  have h64 : Nat.card ↥((fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g).map
      (MulAut.conj h).toMonoidHom) = 2 ^ 6 := by
    rw [card_map_conj, S.card_UWg]
    norm_num
  have hle : (fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g).map (MulAut.conj h).toMonoidHom ≤
      L.map (MulAut.conj h).toMonoidHom ⊓ (pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ) :=
    le_inf (Subgroup.map_mono S.TL_le_L) (conj_TL_le_R S hσW hσQ hσ2 hhH hσh)
  have hRT : pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ ≤ T :=
    sup_le S.QT (Subgroup.zpowers_le.mpr hσT)
  set R := pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ
  set L₀ := L.map (MulAut.conj h).toMonoidHom
  have hge := Subgroup.card_le_of_le hle
  rw [h64] at hge
  have hp : IsPGroup 2 ↥(L₀ ⊓ R) := S.hyp.fsu.sylow.1.to_le (inf_le_right.trans hRT)
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).mp hp
  have hdvd : Nat.card ↥(L₀ ⊓ R) ∣ Nat.card L₀ := Subgroup.card_dvd_of_le inf_le_left
  rw [hL₀c, he, show (1344 : ℕ) = 2 ^ 6 * 21 by norm_num] at hdvd
  have h2 : 2 ^ e ∣ 2 ^ 6 :=
    (Nat.Coprime.pow_left e (by norm_num : Nat.Coprime 2 21)).dvd_of_dvd_mul_right hdvd
  have h3 : 2 ^ e ≤ 2 ^ 6 := Nat.le_of_dvd (by norm_num) h2
  rw [he] at hge ⊢
  exact le_antisymm h3 hge

theorem isSylowTwoOf_R {σ h : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hhH : h ∈ l32nH T V)
    (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V)) (hσT : σ ∈ T) :
    QuasithinUnique.IsSylowTwoOf (pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ)
      (L.map (MulAut.conj h).toMonoidHom ⊔ (pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ)) := by
  have hL₀c : Nat.card ↥(L.map (MulAut.conj h).toMonoidHom) = 1344 := by
    rw [card_map_conj, S.cardL]
  have hinf := card_inf_R S hσW hσQ hσ2 hhH hσh hσT
  have hRN := R_le_normalizer S hσT hhH hσh
  have hRT : pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ ≤ T :=
    sup_le S.QT (Subgroup.zpowers_le.mpr hσT)
  set R := pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ
  set L₀ := L.map (MulAut.conj h).toMonoidHom
  have h1 : L₀.relIndex (R ⊔ L₀) = L₀.relIndex R := relIndex_sup_eq_of_le_normalizer hRN
  have h2 := Subgroup.relIndex_mul_card L₀ (R ⊔ L₀)
  rw [inf_eq_left.mpr le_sup_right, h1, hL₀c] at h2
  have h3 := Subgroup.relIndex_mul_card L₀ R
  rw [hinf] at h3
  have h4 := Subgroup.relIndex_mul_card R (R ⊔ L₀)
  rw [inf_eq_left.mpr le_sup_left] at h4
  have hpos : 0 < Nat.card R := Nat.card_pos
  have hidx : R.relIndex (R ⊔ L₀) = 21 := by
    have h5 : R.relIndex (R ⊔ L₀) * Nat.card R = 21 * Nat.card R := by
      rw [h4, ← h2, ← h3]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h5
  refine ⟨le_sup_right, S.hyp.fsu.sylow.1.to_le hRT, ?_⟩
  show ¬ 2 ∣ R.relIndex (L₀ ⊔ R)
  rw [sup_comm, hidx]
  decide

theorem isLocal_R {σ h : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hσQ : σ ∉ pCoreOf 2 (l32nH T V)) (hσ2 : σ * σ = 1) (hhH : h ∈ l32nH T V)
    (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V)) (hσT : σ ∈ T) :
    quasithinIsLocal (pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ)
      (L.map (MulAut.conj h).toMonoidHom) := by
  set R := pCoreOf 2 (l32nH T V) ⊔ Subgroup.zpowers σ
  set L₀ := L.map (MulAut.conj h).toMonoidHom
  have hRN : R ≤ Subgroup.normalizer (L₀ : Set G) := R_le_normalizer S hσT hhH hσh
  have hLc : L ∈ cComp (L ⊔ T) := cComp_of_isLocal S.hyp.fsu.faithful.1
  have hLc' := cComp_map_mulEquiv (MulAut.conj h) hLc
  rw [Subgroup.map_sup] at hLc'
  have hC : L₀ ∈ cComp (L₀ ⊔ R) :=
    cComp_mem_of_le hLc' le_sup_left (sup_le_sup_left (R_le_conj_T S hσT hhH hσh) _)
  have hVn : L₀ ⊔ R ≤ Subgroup.normalizer
      ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) :=
    sup_le (conj_T_le_normalizer S.L_le_normV h) ((R_le_conj_T S hσT hhH hσh).trans
      (conj_T_le_normalizer (le_sup_right.trans S.normV) h))
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using S.elem.2 x x.2)⟩
  have hVO : V.map (MulAut.conj h).toMonoidHom ≤ pCoreOf 2 (L₀ ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((Subgroup.map_mono S.V_le_L).trans le_sup_left) hVn
      (hV2.map _)
  have hV1 : V.map (MulAut.conj h).toMonoidHom ≠ ⊥ := by
    intro hb
    have h8 := card_map_conj V h
    rw [hb, Subgroup.card_bot, S.card8] at h8
    exact absurd h8 (by norm_num)
  exact isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_R S hσW hσQ hσ2 hhH hσh hσT)
    (fun hb => hV1 (le_bot_iff.mp (hb ▸ hVO))) hC

omit [Finite G] S in
theorem mem_pCoreOf_centralizer {t : G} (ht : IsPGroup 2 ↥(Subgroup.zpowers t)) :
    t ∈ pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) := by
  refine le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr ?_) (fun x hx => ?_) ht
    (Subgroup.mem_zpowers t)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · have hc : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hc.zpow_right k).symm.eq

theorem exists_cComp (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hRest : Lemma14323Rest)
    {σ h t : G} (hσW : σ ∈ CFSG.conjugate (l32nW T V V₂) g) (hσQ : σ ∉ pCoreOf 2 (l32nH T V))
    (hσ2 : σ * σ = 1) (hhH : h ∈ l32nH T V) (hσh : σ * h * σ⁻¹ * h⁻¹ ∈ pCoreOf 2 (l32nH T V))
    (hσT : σ ∈ T) (htT : t ∈ T) (htZ : t ∈ Subgroup.centralizer (T : Set G)) (ht1 : t ≠ 1)
    (htL : L.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ K₀ ∈ cComp (Subgroup.centralizer ({t} : Set G)), L.map (MulAut.conj h).toMonoidHom ≤ K₀ := by
  have hTX : T ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htZ x hx)
  have hTS := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTX
  have htp : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    S.hyp.fsu.sylow.1.to_le (Subgroup.zpowers_le.mpr htT)
  have hO : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ := fun hb =>
    ht1 (by have := mem_pCoreOf_centralizer htp; rwa [hb, Subgroup.mem_bot] at this)
  exact lemma_1_2_5_exists S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian h37 h39 hO hTS
    (sup_le S.QT (Subgroup.zpowers_le.mpr hσT)) (relIndex_R_le S hRest hσT hσQ)
    (isLocal_R S hσW hσQ hσ2 hhH hσh hσT) htL

end Setup

end L1444CTL

end CFSG.Quasithin.H13
