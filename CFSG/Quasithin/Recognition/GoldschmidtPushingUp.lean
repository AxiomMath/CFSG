module

public import CFSG.Quasithin.Recognition.GoldschmidtCompletion

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

theorem gold_relIndex_inf_normalCore_le_eight {A : Type*} [Group A] [Finite A]
    {E P Q : Subgroup A} [hQ : Q.Normal] (hE : E.index = 3) (hPE : P ≤ E)
    (hP2 : P.relIndex E ∣ 2) (hQE : Q ≤ E) : (Q ⊓ P.normalCore).relIndex Q ≤ 8 := by
  classical
  have hPnormE : ∀ e ∈ E, ∀ p ∈ P, e * p * e⁻¹ ∈ P := by
    have hN : (P.subgroupOf E).Normal := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hP2 with h | h
      · have hEP : E ≤ P := Subgroup.relIndex_eq_one.mp h
        have : P.subgroupOf E = ⊤ := Subgroup.subgroupOf_eq_top.mpr hEP
        rw [this]
        infer_instance
      · exact Subgroup.normal_of_index_eq_two h
    intro e he p hp
    have hp' : (⟨p, hPE hp⟩ : E) ∈ P.subgroupOf E := hp
    exact hN.conj_mem _ hp' ⟨e, he⟩
  let F : A → Subgroup A := fun a => Q ⊓ P.map (MulAut.conj a).toMonoidHom
  have hF_mem : ∀ a x, x ∈ F a ↔ x ∈ Q ∧ a⁻¹ * x * a ∈ P := by
    intro a x
    constructor
    · rintro ⟨hxQ, q, hq, rfl⟩
      refine ⟨hxQ, ?_⟩
      have : a⁻¹ * (a * q * a⁻¹) * a = q := by group
      show a⁻¹ * (a * q * a⁻¹) * a ∈ P
      rw [this]
      exact hq
    · rintro ⟨hxQ, h⟩
      exact ⟨hxQ, a⁻¹ * x * a, h, by simp [mul_assoc]⟩
  have hFcoset : ∀ a, ∀ e ∈ E, F (a * e) = F a := by
    intro a e he
    ext x
    rw [hF_mem, hF_mem]
    have hy : a⁻¹ * x * a = e * ((a * e)⁻¹ * x * (a * e)) * e⁻¹ := by group
    constructor
    · rintro ⟨hxQ, h⟩
      refine ⟨hxQ, ?_⟩
      rw [hy]
      exact hPnormE e he _ h
    · rintro ⟨hxQ, h⟩
      refine ⟨hxQ, ?_⟩
      have hy' : (a * e)⁻¹ * x * (a * e) = e⁻¹ * (a⁻¹ * x * a) * e⁻¹⁻¹ := by group
      rw [hy']
      exact hPnormE e⁻¹ (inv_mem he) _ h
  have hQmap : ∀ a : A, Q.map (MulAut.conj a).toMonoidHom = Q := by
    intro a
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa using hQ.conj_mem e he a
    · intro hx
      exact ⟨a⁻¹ * x * a, by simpa using hQ.conj_mem x hx a⁻¹, by simp [mul_assoc]⟩
  have hPE_ne : P.relIndex E ≠ 0 := fun h0 => by
    rw [h0] at hP2
    exact absurd (Nat.eq_zero_of_zero_dvd hP2) (by norm_num)
  have hPQ : P.relIndex Q ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hQE hPE_ne).trans (Nat.le_of_dvd (by norm_num) hP2)
  have hFrel : ∀ a, (F a).relIndex Q ≤ 2 := by
    intro a
    have hinj : Function.Injective (MulAut.conj a).toMonoidHom := (MulAut.conj a).injective
    have h1 := Subgroup.relIndex_map_map_of_injective P Q hinj
    rw [hQmap a] at h1
    have h2 : (F a).relIndex Q = (P.map (MulAut.conj a).toMonoidHom).relIndex Q := by
      show (Q ⊓ P.map (MulAut.conj a).toMonoidHom).relIndex Q = _
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h2, h1]
    exact hPQ
  have : Fintype (A ⧸ E) := Fintype.ofFinite _
  let G : A ⧸ E → Subgroup A := fun x => F x.out
  have hcard : Fintype.card (A ⧸ E) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hE]
  have hG2 : ∀ x, (G x).relIndex Q ≤ 2 := fun x => hFrel _
  have hbound : (⨅ x, G x).relIndex Q ≤ 8 := by
    refine (Subgroup.relIndex_iInf_le G).trans ?_
    calc ∏ x, (G x).relIndex Q ≤ 2 ^ (Finset.univ : Finset (A ⧸ E)).card :=
          Finset.prod_le_pow_card _ _ _ (fun x _ => hG2 x)
      _ = 8 := by rw [Finset.card_univ, hcard]; norm_num
  have hle : (⨅ x, G x) ≤ Q ⊓ P.normalCore := by
    intro w hw
    have hwQ : w ∈ Q := ((hF_mem _ w).mp (Subgroup.mem_iInf.mp hw (QuotientGroup.mk 1 : A ⧸ E))).1
    refine ⟨hwQ, fun b => ?_⟩
    obtain ⟨e, he⟩ := QuotientGroup.mk_out_eq_mul E b⁻¹
    have hw' : w ∈ F ((QuotientGroup.mk b⁻¹ : A ⧸ E).out) := Subgroup.mem_iInf.mp hw _
    rw [he, hFcoset _ e e.2, hF_mem] at hw'
    simpa using hw'.2
  have hne : (⨅ x, G x).relIndex Q ≠ 0 :=
    Subgroup.relIndex_iInf_ne_zero fun x => by
      intro h0
      have := Subgroup.relIndex_dvd_card (H := G x) (K := Q)
      rw [h0] at this
      exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd this)
  exact (Subgroup.relIndex_le_of_le_left hle hne).trans hbound

theorem gold_sup_zpowers_eq_top {B : Type*} [Group B] {H : Subgroup B} (hH : H.index = 3) {d : B}
    (hd : d ∉ H) : H ⊔ Subgroup.zpowers d = ⊤ := by
  have hdvd : (H ⊔ Subgroup.zpowers d).index ∣ 3 := by
    rw [← hH]
    exact Subgroup.index_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have hmul := Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ Subgroup.zpowers d)
    rw [hH, h3] at hmul
    have hrel : H.relIndex (H ⊔ Subgroup.zpowers d) = 1 := by omega
    have hle : H ⊔ Subgroup.zpowers d ≤ H := Subgroup.relIndex_eq_one.mp hrel
    exact hd (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))

namespace GoldAmalgam

variable {A C B : Type*} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem card_le_sixteen_of_centralizing [Finite A] (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) {d : B} (hd : d ∉ X.edgeB)
    (hdc : ∀ q ∈ X.edgeB.normalCore, d * q = q * d) : Nat.card C ≤ 16 := by
  let P : Subgroup A := X.coreB.map X.toA
  have hPE : P ≤ X.edgeA := Subgroup.map_le_range _ _
  have hPrel : P.relIndex X.edgeA ∣ 2 := by
    have := Subgroup.relIndex_map_map_of_injective X.coreB ⊤ X.toA_injective
    rw [Subgroup.map_top, Subgroup.relIndex_top_right] at this
    exact this ▸ X.coreB_index_dvd_two hB
  let W : Subgroup A := P.normalCore
  have hWle : W ≤ X.edgeA := P.normalCore_le.trans hPE
  have hWle' : W ≤ P := P.normalCore_le
  let WC : Subgroup C := W.comap X.toA
  have hWmap : WC.map X.toA = W := Subgroup.map_comap_eq_self hWle
  have hWnorm : (WC.map X.toA).Normal := by
    rw [hWmap]
    exact Subgroup.normalCore_normal P
  have hWCnorm : WC.Normal := Subgroup.Normal.comap (Subgroup.normalCore_normal P) X.toA
  have hWCle : WC ≤ X.coreB := by
    intro c hc
    obtain ⟨c', hc', hcc'⟩ := hWle' hc
    have : c' = c := X.toA_injective hcc'
    rwa [← this]
  have hBnorm : (WC.map X.toB).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp ?_
    rw [eq_top_iff, ← gold_sup_zpowers_eq_top hB hd]
    refine sup_le ?_ ?_
    · exact GoldCompletion.range_le_normalizer_map X.toB WC
    · rw [Subgroup.zpowers_le]
      have hNle : WC.map X.toB ≤ X.edgeB.normalCore :=
        calc WC.map X.toB ≤ X.coreB.map X.toB := Subgroup.map_mono hWCle
          _ = X.edgeB.normalCore := X.swap.map_coreA
      have hcomm : ∀ h ∈ WC.map X.toB, d * h * d⁻¹ = h := by
        intro h hh
        rw [hdc h (hNle hh)]
        simp
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [hcomm h hh]
        exact hh
      · intro hh
        have hcomm' := hdc _ (hNle hh)
        have e : d⁻¹ * (d * h * d⁻¹) * d = d * h * d⁻¹ := by
          calc d⁻¹ * (d * h * d⁻¹) * d = d⁻¹ * ((d * h * d⁻¹) * d) := by group
            _ = d⁻¹ * (d * (d * h * d⁻¹)) := by rw [hcomm']
            _ = d * h * d⁻¹ := by group
        have e2 : d⁻¹ * (d * h * d⁻¹) * d = h := by group
        rw [e2] at e
        rw [e]
        exact hh
  have hWeq : W = ⊥ := by
    have h0 : WC = ⊥ := hf WC hWnorm hBnorm
    rw [← hWmap, h0, Subgroup.map_bot]
  let Q : Subgroup A := X.edgeA.normalCore
  have hQE : Q ≤ X.edgeA := X.edgeA.normalCore_le
  have h8 := gold_relIndex_inf_normalCore_le_eight (E := X.edgeA) (P := P) (Q := Q) hA hPE
    hPrel hQE
  have hWeq' : P.normalCore = ⊥ := hWeq
  rw [hWeq', inf_bot_eq, Subgroup.relIndex_bot_left] at h8
  have hcardE : Nat.card X.edgeA = X.coreA.index * Nat.card Q := by
    have h1 := Subgroup.card_mul_index (Q.subgroupOf X.edgeA)
    have h2 : Nat.card (Q.subgroupOf X.edgeA) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv
    rw [h2] at h1
    rw [X.coreA_index_eq, ← h1]
    unfold Subgroup.relIndex
    ring
  have hcardC : Nat.card X.edgeA = Nat.card C :=
    Nat.card_congr (MonoidHom.ofInjective X.toA_injective).toEquiv.symm
  have hcore2 : X.coreA.index ≤ 2 := Nat.le_of_dvd (by norm_num) (X.coreA_index_dvd_two hA)
  calc Nat.card C = Nat.card X.edgeA := hcardC.symm
    _ = X.coreA.index * Nat.card Q := hcardE
    _ ≤ 2 * 8 := Nat.mul_le_mul hcore2 h8
    _ = 16 := by norm_num

theorem exists_centralizing_not_mem_edgeB (hQ : ¬ Subgroup.centralizer
    (X.edgeB.normalCore : Set B) ≤ X.edgeB.normalCore) :
    ∃ d : B, d ∉ X.edgeB ∧ ∀ q ∈ X.edgeB.normalCore, d * q = q * d := by
  by_contra hcon
  push Not at hcon
  apply hQ
  have hnorm : (Subgroup.centralizer (X.edgeB.normalCore : Set B)).Normal :=
    Subgroup.normal_centralizer
  have hle : Subgroup.centralizer (X.edgeB.normalCore : Set B) ≤ X.edgeB := by
    intro d hd
    by_contra hdE
    obtain ⟨q, hq, hne⟩ := hcon d hdE
    exact hne (Subgroup.mem_centralizer_iff.mp hd q hq).symm
  rw [← Subgroup.normal_le_normalCore] at hle
  exact hle

variable [Finite A] [Finite C] [Finite B]

theorem card_le_sixteen_of_not_centralizer_le (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3)
    (h : ¬ Subgroup.centralizer (pCore 2 B : Set B) ≤ pCore 2 B) : Nat.card C ≤ 16 := by
  rw [← X.normalCore_edgeB_eq_pCore hf hA hB] at h
  obtain ⟨d, hd, hdc⟩ := X.exists_centralizing_not_mem_edgeB h
  exact X.card_le_sixteen_of_centralizing hf hA hB hd hdc

theorem card_le_sixteen_of_not_centralizer_le_A (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3)
    (h : ¬ Subgroup.centralizer (pCore 2 A : Set A) ≤ pCore 2 A) : Nat.card C ≤ 16 :=
  X.swap.card_le_sixteen_of_not_centralizer_le ((X.swap_isFaithful_iff).mpr hf) hB hA h

end GoldAmalgam

end CFSG.Quasithin
