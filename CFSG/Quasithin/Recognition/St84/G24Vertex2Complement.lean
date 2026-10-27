module

import CFSG.GH74.QTGen4.U42.CoordsB
import CFSG.Quasithin.Recognition.St84.G24Tools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.Quasithin.Recognition.St84.G24Data

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open CFSG.QuasithinUnique.A5.Delta5 (Alt5 a5_card)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

private theorem centralizer_complement_data [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) {k : G} (hkB : k ∈ bigB L1 L2 S) (hk3 : orderOf k = 3)
    (hkc : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L2 L1 S)
    (hkZ : ∀ z ∈ centerOf (dsQ L2 L1 S), k * z = z * k)
    (hkQ : dsQ L2 L1 S ⊓ Subgroup.centralizer ({k} : Set G) = centerOf (dsQ L2 L1 S)) :
    ∃ C : Subgroup G,
      C = (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) ∧
      centerOf (dsQ L2 L1 S) ≤ C ∧
      C ≤ Subgroup.normalizer (centerOf (dsQ L2 L1 S) : Set G) ∧
      C ⊓ dsQ L2 L1 S = centerOf (dsQ L2 L1 S) ∧
      Nat.card C = 2880 ∧
      (∀ x ∈ L2 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L2 L1 S, ∃ c ∈ C, x = q * c) := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  let Ck : Subgroup G := Subgroup.centralizer ({k} : Set G)
  let C : Subgroup G := P2 ⊓ Ck
  have hQ2P2 : Q2 ≤ P2 := dsQ_le_P_right L1 L2 S
  have hP2N : P2 ≤ Subgroup.normalizer (Q2 : Set G) := P_le_normalizer_dsQ_right L1 L2 S
  have hZ2Q2 : Z2 ≤ Q2 := inf_le_left
  have hZ2N : P2 ≤ Subgroup.normalizer (Z2 : Set G) :=
    P_le_normalizer_centerOf_dsQ_right L1 L2 S
  have hP2card : Nat.card P2 = 2 ^ 12 * 45 := G24LocalData.card_vertex_right hF h2 hD
  have hQ2card : Nat.card Q2 = 2 ^ 10 := hD.card_right
  have hZ2card : Nat.card Z2 = 2 ^ 4 := hD.card_center_right
  have hZ2special : IsSpecialPGroup 2 ↥Q2 := hD.special_right
  have hQ2_2 : IsPGroup 2 ↥Q2 := hZ2special.1
  have hZ2exp : ∀ z ∈ Z2, z ^ 2 = 1 := fun z hz =>
    hD.sq_eq_one_of_mem_centerOf_right hz
  have hZ2comm : ∀ a ∈ Z2, ∀ b ∈ Z2, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp hb.2 a (hZ2Q2 ha)
  have hZ2C : Z2 ≤ C := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hQ2P2 (hZ2Q2 hz), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hkZ z hz).symm
  have hCN : C ≤ Subgroup.normalizer (Z2 : Set G) := fun c hc => hZ2N hc.1
  have hcomp : ∀ x ∈ P2, ∃ q ∈ Q2, ∃ c ∈ C, x = q * c := by
    intro x hx
    obtain ⟨q, hq, c, hc, rfl⟩ := CFSG.Quasithin.St84.exists_centralizer_complement
      (P := P2) (Q := Q2) hQ2P2 hP2N hQ2_2
      ((le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) hkB) hk3
      (fun y hy => by simpa [commutatorElement_def] using hkc y hy) x hx
    exact ⟨q, hq, c, hc, rfl⟩
  have hCinf : C ⊓ Q2 = Z2 := by
    dsimp only [C, Ck, Z2]
    rw [inf_assoc, inf_comm Ck Q2, ← inf_assoc, inf_eq_right.mpr hQ2P2, hkQ]
  have hsupQC : Q2 ⊔ C = P2 := by
    refine le_antisymm (sup_le hQ2P2 inf_le_left) ?_
    intro x hx
    obtain ⟨q, hq, c, hc, rfl⟩ := hcomp x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hc)
  have hCinf' : Q2 ⊓ C = Z2 := by rw [inf_comm]; exact hCinf
  have hCNQ : C ≤ Subgroup.normalizer (Q2 : Set G) := fun c hc => hP2N hc.1
  have hCcard : Nat.card C = 2880 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := Q2) (B := C) hCNQ
    rw [hsupQC, hCinf', hP2card, hQ2card, hZ2card] at h
    norm_num at h ⊢
    omega
  exact ⟨C, rfl, hZ2C, hCN, hCinf, hCcard, hcomp⟩

private theorem exists_gaschutz_complement [Finite G]
    {L1 L2 S : Subgroup G} (hD : G24LocalData L1 L2 S) {C : Subgroup G}
    (hZ2C : centerOf (dsQ L2 L1 S) ≤ C)
    (hCN : C ≤ Subgroup.normalizer (centerOf (dsQ L2 L1 S) : Set G))
    (hCcard : Nat.card C = 2880) {Y : Subgroup G} (hYC : Y ≤ C)
    (hYcard : Nat.card Y = 4) (hYinf : Y ⊓ centerOf (dsQ L2 L1 S) = ⊥) :
    ∃ A : Subgroup G, A ≤ C ∧ A ⊓ centerOf (dsQ L2 L1 S) = ⊥ ∧
      Nat.card A = 180 ∧
      (∀ c ∈ C, ∃ z ∈ centerOf (dsQ L2 L1 S), ∃ a ∈ A, c = z * a) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let T : Subgroup G := Z2 ⊔ Y
  have hYT : Y ≤ T := le_sup_right
  have hZ2T : Z2 ≤ T := le_sup_left
  have hTC : T ≤ C := sup_le hZ2C hYC
  have hYN : Y ≤ Subgroup.normalizer (Z2 : Set G) := hYC.trans hCN
  have hZ2card : Nat.card Z2 = 2 ^ 4 := hD.card_center_right
  have hTcard : Nat.card T = 64 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := Z2) (B := Y) hYN
    have hinf : Z2 ⊓ Y = ⊥ := by rw [inf_comm]; exact hYinf
    rw [hinf, hZ2card, hYcard, Subgroup.card_bot] at h
    simpa [T] using h
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 6) (by rw [hTcard]; norm_num)
  have hTCindex : ¬ 2 ∣ (T.subgroupOf C).index := by
    have hcardsub : Nat.card ↥(T.subgroupOf C) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
    have h := Subgroup.index_mul_card (T.subgroupOf C)
    rw [hcardsub, hTcard, hCcard] at h
    intro h2
    rcases h2 with ⟨m, hm⟩
    rw [hm] at h
    omega
  have hdecT : ∀ t ∈ T, ∃ v ∈ Z2, ∃ y ∈ Y, v * y = t := by
    intro t ht
    obtain ⟨v, hv, y, hy, hvy⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hYN).mp (by
        simpa [T] using ht)
    exact ⟨v, hv, y, hy, hvy.symm⟩
  have hVn : ∀ h ∈ C, ∀ v ∈ Z2, h * v * h⁻¹ ∈ Z2 := by
    intro h hh v hv
    exact (Subgroup.mem_normalizer_iff.mp (hCN hh) v).mp hv
  have hZ2_2 : IsPGroup 2 Z2 :=
    hD.special_right.1.to_le (show centerOf (dsQ L2 L1 S) ≤ dsQ L2 L1 S from inf_le_left)
  have hZ2comm : ∀ a ∈ Z2, ∀ b ∈ Z2, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp hb.2 a (Subgroup.mem_inf.mp ha).1
  obtain ⟨A, hAC, hAZ2bot, hZ2A⟩ := CFSG.GH74.QTGen4.U42.gaschutzSplitU
    (H := C) (V := Z2) (T := T) (K0 := Y) hZ2C hZ2T hTC hVn hZ2_2 hZ2comm hT2
    hTCindex hYT (by rw [inf_comm]; exact hYinf) hdecT
  have hAZ2N : A ≤ Subgroup.normalizer (Z2 : Set G) := hAC.trans hCN
  have hAcard : Nat.card A = 180 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := Z2) (B := A) hAZ2N
    rw [hZ2A, inf_comm, hAZ2bot, hZ2card, hCcard] at h
    simp only [Subgroup.card_bot, mul_one] at h
    omega
  refine ⟨A, hAC, hAZ2bot, hAcard, ?_⟩
  intro c hc
  exact (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hAZ2N).mp (by
    rw [hZ2A]; exact hc)

private theorem k_mem_of_complement [Finite G] {A C Z2 : Subgroup G} {k : G}
    (hAdecomp : ∀ c ∈ C, ∃ z ∈ Z2, ∃ a ∈ A, c = z * a)
    (hZ2exp : ∀ z ∈ Z2, z ^ 2 = 1) (hkZ : ∀ z ∈ Z2, k * z = z * k)
    (hAZ2bot : A ⊓ Z2 = ⊥) (hkC : k ∈ C) (hk3 : orderOf k = 3) : k ∈ A := by
  obtain ⟨z, hz, a, ha, hza⟩ := hAdecomp k hkC
  have hzk : k * z = z * k := hkZ z hz
  have hz3 : z ^ 3 = z := by
    rw [show z ^ 3 = z ^ 2 * z by group, hZ2exp z hz, one_mul]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hZ2exp z hz)
  have h3 : a ^ 3 = z := by
    have hza' : a = z⁻¹ * k := by
      calc a = z⁻¹ * (z * a) := by group
        _ = z⁻¹ * k := by rw [← hza]
    have hkpow : k ^ 3 = 1 := by
      rw [← hk3]
      exact pow_orderOf_eq_one k
    have hcomm : Commute z⁻¹ k := (show Commute z k from hzk.symm).inv_left
    calc a ^ 3 = (z⁻¹ * k) ^ 3 := by rw [hza']
      _ = (z⁻¹) ^ 3 * k ^ 3 := hcomm.mul_pow 3
      _ = z := by rw [hkpow, mul_one, inv_pow, hz3, hzinv]
  have hzmemA : z ∈ A := by rw [← h3]; exact A.pow_mem ha 3
  have hzbot : z ∈ A ⊓ Z2 := ⟨hzmemA, hz⟩
  rw [hAZ2bot, Subgroup.mem_bot] at hzbot
  rw [hzbot, one_mul] at hza
  exact hza ▸ ha

theorem G24Vertex2.exists_complement_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) {k : G} (hkB : k ∈ bigB L1 L2 S) (hk3 : orderOf k = 3)
    (hkc : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L2 L1 S)
    (hkZ : ∀ z ∈ centerOf (dsQ L2 L1 S), k * z = z * k)
    (hkQ : dsQ L2 L1 S ⊓ Subgroup.centralizer ({k} : Set G) = centerOf (dsQ L2 L1 S))
    (hY : ∃ Y : Subgroup G, Y ≤ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) ∧
      Nat.card Y = 4 ∧ Y ⊓ centerOf (dsQ L2 L1 S) = ⊥) :
    ∃ A : Subgroup G, A ≤ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) ∧
      A ⊓ dsQ L2 L1 S = ⊥ ∧ Nat.card A = 180 ∧ k ∈ A ∧
      (∀ x ∈ L2 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L2 L1 S, ∃ c ∈ A, x = q * c) := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  obtain ⟨C, hCdef, hZ2C, hCN, hCinf, hCcard, hCcomp⟩ :=
    centralizer_complement_data hF h2 hD hkB hk3 hkc hkZ hkQ
  obtain ⟨Y, hYle, hYcard, hYinf⟩ := hY
  have hYC : Y ≤ C := hCdef ▸ hYle
  obtain ⟨A, hAC, hAZ2bot, hAcard, hAdecomp⟩ :=
    exists_gaschutz_complement hD hZ2C hCN hCcard hYC hYcard hYinf
  have hZ2Q2 : centerOf Q2 ≤ Q2 := inf_le_left
  have hAinfQ : A ⊓ Q2 = ⊥ := by
    refine le_bot_iff.mp ?_
    have h1 : A ⊓ Q2 ≤ centerOf Q2 :=
      (inf_le_inf hAC (le_refl Q2)).trans (le_of_eq hCinf)
    have h2 : A ⊓ Q2 ≤ A ⊓ centerOf Q2 := le_inf inf_le_left h1
    rw [hAZ2bot] at h2
    exact h2
  have hkC : k ∈ C := by
    rw [hCdef]
    refine Subgroup.mem_inf.mpr ⟨(le_sup_right :
      bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) hkB, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hkA : k ∈ A :=
    k_mem_of_complement hAdecomp
      (fun z hz => hD.sq_eq_one_of_mem_centerOf_right hz) hkZ hAZ2bot hkC hk3
  refine ⟨A, ?_, hAinfQ, hAcard, hkA, ?_⟩
  · intro x hx
    exact ⟨(hCdef ▸ inf_le_left) (hAC hx), (hCdef ▸ inf_le_right) (hAC hx)⟩
  · intro x hx
    obtain ⟨q, hq, c, hc, rfl⟩ := hCcomp x hx
    obtain ⟨z, hz, a, ha, rfl⟩ := hAdecomp c hc
    exact ⟨q * z, Q2.mul_mem hq (hZ2Q2 hz), a, ha, (mul_assoc q z a).symm⟩

private theorem closure_eq_top_of_orderOf_two_three_five {s t : Alt5}
    (hs : orderOf s = 2) (ht : orderOf t = 3) (hst : orderOf (s * t) = 5) :
    Subgroup.closure ({s, t} : Set Alt5) = ⊤ := by
  set N : Subgroup Alt5 := Subgroup.closure ({s, t} : Set Alt5) with hN
  have hsN : s ∈ N := Subgroup.subset_closure (by simp)
  have htN : t ∈ N := Subgroup.subset_closure (by simp)
  have hstN : s * t ∈ N := N.mul_mem hsN htN
  have d5 : 5 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hstN
    rwa [hst] at this
  have d2 : 2 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hsN
    rwa [hs] at this
  have d3 : 3 ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N htN
    rwa [ht] at this
  have h30 : 30 ∣ Nat.card N := by omega
  have hdvd : Nat.card N ∣ 60 := by
    rw [← a5_card]
    exact Subgroup.card_subgroup_dvd_card N
  have hle : Nat.card N ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hcases : Nat.card N = 30 ∨ Nat.card N = 60 := by
    obtain ⟨k, hk⟩ := h30
    omega
  have hsimple : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
  rcases hcases with h | h
  · exfalso
    have hidx : N.index = 2 := by
      have := N.card_mul_index
      rw [a5_card, h] at this
      omega
    have hnorm : N.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · rw [h1] at h; simp at h
    · rw [h1] at hidx; simp at hidx
  · exact (Subgroup.card_eq_iff_eq_top N).mp (by
      rw [h, a5_card])



theorem G24Vertex2.card_inf_L2_of_complement [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) {A : Subgroup G}
    (hAP2 : A ≤ L2 ⊔ bigB L1 L2 S) (hAcard : Nat.card A = 180)
    (hdecomp : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L2 L1 S, ∃ c ∈ A, x = q * c) :
    Nat.card ↥(A ⊓ L2) = 60 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ2eq : pCoreOf 2 L2 = dsQ L2 L1 S := G24LocalData.pCoreOf_eq_dsQ_right hR hD.le_right
  have hQ2L2 : dsQ L2 L1 S ≤ L2 := by
    rw [← hQ2eq]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 L2
  have hP2card : Nat.card ↥(L2 ⊔ bigB L1 L2 S) = 2 ^ 12 * 45 :=
    G24LocalData.card_vertex_right hF h2 hD
  have hQ2card : Nat.card (dsQ L2 L1 S) = 2 ^ 10 := hD.card_right
  have hAN : A ≤ Subgroup.normalizer (L2 : Set G) :=
    hAP2.trans (G24LocalData.normal_L_right hR)
  have hsup : L2 ⊔ A = L2 ⊔ bigB L1 L2 S := by
    refine le_antisymm (sup_le le_sup_left hAP2) ?_
    intro x hx
    obtain ⟨q, hq, c, hc, rfl⟩ := hdecomp x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hQ2L2 hq)) (Subgroup.mem_sup_right hc)
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := L2) (B := A) hAN
  rw [hsup, inf_comm, hAcard, hP2card] at h
  have hL : Nat.card L2 = 60 * Nat.card (dsQ L2 L1 S) := G24LocalData.card_L_right hF h2 hD
  rw [hL, hQ2card] at h
  norm_num at h ⊢
  omega

private theorem ker_comp_inclusion_eq_bot [Finite G]
    {L1 L2 S : Subgroup G} {A : Subgroup G}
    (hQ2eq : pCoreOf 2 L2 = dsQ L2 L1 S)
    (hAinf : A ⊓ dsQ L2 L1 S = ⊥) (e : oTwoQuot ↥L2 ≃* Alt5) :
    (e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 ↥L2)).comp
      (Subgroup.inclusion (inf_le_right : A ⊓ L2 ≤ L2)))).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : (QuotientGroup.mk' (pCore 2 ↥L2))
      (Subgroup.inclusion (inf_le_right : A ⊓ L2 ≤ L2) x) = 1 :=
    e.injective (by simpa using hx)
  have h2 : Subgroup.inclusion (inf_le_right : A ⊓ L2 ≤ L2) x ∈ pCore 2 ↥L2 :=
    QuotientGroup.eq_one_iff _ |>.mp h1
  have h3 : (x : G) ∈ pCoreOf 2 L2 :=
    Subgroup.mem_map.mpr ⟨Subgroup.inclusion (inf_le_right : A ⊓ L2 ≤ L2) x, h2, rfl⟩
  have hxQ : (x : G) ∈ dsQ L2 L1 S := by rwa [hQ2eq] at h3
  have hxbot : (x : G) ∈ A ⊓ dsQ L2 L1 S := ⟨x.2.1, hxQ⟩
  rw [hAinf, Subgroup.mem_bot] at hxbot
  rw [Subgroup.mem_bot]
  exact Subtype.ext hxbot

private theorem closure_psi_eq_top [Finite G] {H : Subgroup G} {a b : G}
    {ψ : ↥H →* Alt5} (aH bH : ↥H) (haH : (aH : G) = a) (hbH : (bH : G) = b)
    (hinj : Function.Injective ψ)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha2 : a ^ 2 = 1) (hb3 : b ^ 3 = 1)
    (hab5 : (a * b) ^ 5 = 1) (hab1 : a * b ≠ 1) :
    Subgroup.closure ({ψ aH, ψ bH} : Set Alt5) = ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have haH2 : aH ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, haH] using ha2
  have hbH3 : bH ^ 3 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, hbH] using hb3
  have habH5 : (aH * bH) ^ 5 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, Subgroup.coe_mul, haH, hbH] using hab5
  have hψa2 : ψ aH ^ 2 = 1 := by
    rw [← map_pow, haH2, map_one]
  have hψa1 : ψ aH ≠ 1 := by
    intro h
    have h1 : aH = 1 := hinj (by rw [h, map_one])
    have h2 : (aH : G) = 1 := congrArg Subtype.val h1
    rw [haH] at h2
    exact ha1 h2
  have hψb3 : ψ bH ^ 3 = 1 := by
    rw [← map_pow, hbH3, map_one]
  have hψb1 : ψ bH ≠ 1 := by
    intro h
    have h1 : bH = 1 := hinj (by rw [h, map_one])
    have h2 : (bH : G) = 1 := congrArg Subtype.val h1
    rw [hbH] at h2
    exact hb1 h2
  have hψab5 : (ψ aH * ψ bH) ^ 5 = 1 := by
    rw [← map_mul, ← map_pow, habH5, map_one]
  have hψab1 : ψ aH * ψ bH ≠ 1 := by
    intro h
    have h1 : ψ (aH * bH) = 1 := by rw [map_mul, h]
    have h2 : aH * bH = 1 := hinj (by rw [h1, map_one])
    have h3 : ((aH * bH : ↥H) : G) = 1 := congrArg Subtype.val h2
    rw [Subgroup.coe_mul, haH, hbH] at h3
    exact hab1 h3
  have haord : orderOf (ψ aH) = 2 := orderOf_eq_prime hψa2 hψa1
  have hbord : orderOf (ψ bH) = 3 := orderOf_eq_prime hψb3 hψb1
  have habord : orderOf (ψ aH * ψ bH) = 5 := orderOf_eq_prime hψab5 hψab1
  exact closure_eq_top_of_orderOf_two_three_five haord hbord habord

private theorem closure_eq_of_psi_bijective [Finite G]
    {H : Subgroup G} {a b : G} {ψ : ↥H →* Alt5}
    (hcl : Subgroup.closure ({a, b} : Set G) ≤ H) (aH bH : ↥H)
    (haH : (aH : G) = a) (hbH : (bH : G) = b)
    (hinj : Function.Injective ψ)
    (hgen : Subgroup.closure ({ψ aH, ψ bH} : Set Alt5) = ⊤)
    (hHcard : Nat.card ↥H = 60) :
    Subgroup.closure ({a, b} : Set G) = H := by
  let φ : ↥(Subgroup.closure ({a, b} : Set G)) →* Alt5 :=
    ψ.comp (Subgroup.inclusion hcl)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : ψ (Subgroup.inclusion hcl x) = ψ (Subgroup.inclusion hcl y) := hxy
    have h2 := hinj h1
    exact Subtype.ext (congrArg (fun z : ↥H => (z : G)) h2)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Subgroup.closure ({ψ aH, ψ bH} : Set Alt5) := by
      rw [hgen]; exact Subgroup.mem_top y
    have hle : Subgroup.closure ({ψ aH, ψ bH} : Set Alt5) ≤ φ.range := by
      refine (Subgroup.closure_le (K := φ.range)).mpr ?_
      intro z hz
      rcases hz with rfl | rfl
      · refine ⟨⟨a, Subgroup.subset_closure (by simp)⟩, ?_⟩
        exact congrArg ψ (Subtype.ext haH.symm)
      · refine ⟨⟨b, Subgroup.subset_closure (by simp)⟩, ?_⟩
        exact congrArg ψ (Subtype.ext hbH.symm)
    obtain ⟨x, hx⟩ := hle hy
    exact ⟨x, hx⟩
  have hcardcl : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 60 := by
    have h1 : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = Nat.card Alt5 :=
      Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
    rw [h1, a5_card]
  exact Subgroup.eq_of_le_of_card_ge hcl (by rw [hcardcl, hHcard])

theorem G24Vertex2.closure_ab_eq_A_inf_L2 [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) {A : Subgroup G}
    (hAP2 : A ≤ L2 ⊔ bigB L1 L2 S) (hAinf : A ⊓ dsQ L2 L1 S = ⊥)
    (hAcard : Nat.card A = 180)
    (hdecomp : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L2 L1 S, ∃ c ∈ A, x = q * c)
    {a b : G} (haA : a ∈ A) (haL : a ∈ L2) (hbA : b ∈ A) (hbL : b ∈ L2)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (ha2 : a ^ 2 = 1) (hb3 : b ^ 3 = 1) (hab5 : (a * b) ^ 5 = 1)
    (hab1 : a * b ≠ 1) :
    Subgroup.closure ({a, b} : Set G) = A ⊓ L2 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let Q2 : Subgroup G := dsQ L2 L1 S
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ2eq : pCoreOf 2 L2 = Q2 := G24LocalData.pCoreOf_eq_dsQ_right hR hD.le_right
  have hcl : Subgroup.closure ({a, b} : Set G) ≤ A ⊓ L2 := by
    refine (Subgroup.closure_le (K := A ⊓ L2)).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨haA, haL⟩
    · exact ⟨hbA, hbL⟩
  have hHcard : Nat.card ↥(A ⊓ L2) = 60 :=
    G24Vertex2.card_inf_L2_of_complement hF h2 hD hAP2 hAcard hdecomp
  let incl : ↥(A ⊓ L2) →* ↥L2 := Subgroup.inclusion inf_le_right
  let ρ : ↥(A ⊓ L2) →* oTwoQuot ↥L2 :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L2)).comp incl
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two h2
  let ψ : ↥(A ⊓ L2) →* Alt5 := e.toMonoidHom.comp ρ
  have hψker : ψ.ker = ⊥ := by
    simpa [ψ, ρ, incl] using ker_comp_inclusion_eq_bot hQ2eq hAinf e
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hψker
  let aH : ↥(A ⊓ L2) := ⟨a, ⟨haA, haL⟩⟩
  let bH : ↥(A ⊓ L2) := ⟨b, ⟨hbA, hbL⟩⟩
  have hgen : Subgroup.closure ({ψ aH, ψ bH} : Set Alt5) = ⊤ :=
    closure_psi_eq_top aH bH rfl rfl hinj ha1 hb1 ha2 hb3 hab5 hab1
  exact closure_eq_of_psi_bijective hcl aH bH rfl rfl hinj hgen hHcard


end CFSG.Quasithin.F112R.St84
