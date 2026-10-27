module

public import CFSG.Quasithin.Vol2.Ch4Sec3C57A5b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCPf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61Base

public section

namespace CFSG.Quasithin.H13.Ch4.C57

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G] {H M₀ R K : Subgroup G}

theorem inf_centralizer_eq_of_im (P : A5Pi K) {A B : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hAB : P.im A = P.im B) :
    blockU K ⊓ Subgroup.centralizer (A : Set G) = blockU K ⊓ Subgroup.centralizer (B : Set G) := by
  have key : ∀ {C : Subgroup G}, C ≤ Subgroup.normalizer (K : Set G) → ∀ {u : G},
      u ∈ blockU K → (u ∈ Subgroup.centralizer (C : Set G) ↔
        ∀ σ ∈ P.im C, vact σ (P.bf u) = P.bf u) := by
    intro C hCN u hu
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hc σ hσ
      obtain ⟨c, hc', rfl⟩ := (P.mem_im_pf hCN).1 hσ
      exact (P.comm_iff (hCN hc') hu).1 (hc c hc')
    · intro hc c hc'
      exact (P.comm_iff (hCN hc') hu).2 (hc _ ((P.mem_im_pf hCN).2 ⟨c, hc', rfl⟩))
  ext u
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hu, hc⟩
    exact ⟨hu, (key hBN hu).2 (hAB ▸ (key hAN hu).1 hc)⟩
  · rintro ⟨hu, hc⟩
    exact ⟨hu, (key hAN hu).2 (hAB.symm ▸ (key hBN hu).1 hc)⟩

namespace Setup

variable (h : Setup H M₀ R K)
include h

omit [Finite G] in
theorem R_le_normalizer_pCoreOf : R ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  h.R_le_H.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)

theorem im_cases (P : A5Pi K) (hR : P.im R = Dstd) {A : Subgroup G} (hA : IsMaxElemAbelian R A)
    (hRA : R ≤ Subgroup.normalizer (A : Set G)) :
    (∀ g, g ∈ P.im A ↔ g = 1) ∨ P.im A = Estd := by
  have hle : P.im A ≤ Dstd := hR ▸ P.im_mono hA.1
  obtain ⟨hsq, hcm⟩ := P.im_elemAbelian hA.2.1
  have hff := P.ff_ineq (isElemAbelian_blockU h.short) h.blockU_le_R h.R_le_normalizer_K hA
  have hfl := card_mul_fix_le (P.im A) hsq hcm
  have hρ : swap (0 : Fin 5) 2 * swap 1 3 ∈ P.im R := by rw [hR]; exact rho_mem_Dset
  have hconj := im_conj_mem P.toPiData hRA _ hρ
  rcases classify_P (P.im A) hle hsq hcm (le_antisymm hfl hff) with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    have h23 := (h1 _).1 (hconj _ ((h1 _).2 (Or.inr rfl)))
    rw [rho_conj.1] at h23
    rcases h23 with h23 | h23
    · exact swaps_ne.2.2 h23
    · exact swaps_ne.1 h23.symm
  · exfalso
    have h01 := (h1 _).1 (hconj _ ((h1 _).2 (Or.inr rfl)))
    rw [rho_conj.2] at h01
    rcases h01 with h01 | h01
    · exact swaps_ne.2.1 h01
    · exact swaps_ne.1 h01
  · right
    ext g
    rw [h1 g, mem_Estd]

theorem eq_pCoreOf_of_im (P : A5Pi K) (hQ : IsMaxElemAbelian R (pCoreOf 2 H)) {A : Subgroup G}
    (hA : IsMaxElemAbelian R A) (h1 : ∀ g, g ∈ P.im A ↔ g = 1) : A = pCoreOf 2 H := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.1.trans h.R_le_normalizer_K
  have hle : A ≤ pCoreOf 2 H := by
    intro a ha
    have hπ : P.π ⟨a, hAN ha⟩ = 1 := (h1 _).1 (P.pi_mem_im (K := A) (y := ⟨a, hAN ha⟩) ha)
    have hc := (P.hker _).1 hπ
    rw [← h.R_inf_centralizer_eq]
    refine ⟨hA.1 ha, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have := hc u hu
    calc u * a = (a * u * a⁻¹) * a := by rw [this]
      _ = a * u := by group
  exact Subgroup.eq_of_le_of_card_ge hle (hA.2.2 _ hQ.1 hQ.2.1)

theorem exists_decomp (h5 : IsAltType K 5) (P : A5Pi K) (hR : P.im R = Dstd) {x : G}
    (hx : x ∈ M₀) (hx1 : ¬ conjSubgroup (blockU K) x ≤ pCoreOf 2 H) {A : Subgroup G}
    (hAR : A ≤ R) (hE : P.im A = Estd) {a : G} (ha : a ∈ A) :
    ∃ v ∈ conjSubgroup (blockU K) x, ∃ u ∈ blockU K, ∃ d ∈ R ⊓ Subgroup.centralizer (K : Set G),
      a = v * (u * d) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hAR.trans h.R_le_normalizer_K
  have hVR : conjSubgroup (blockU K) x ≤ R := h.conj_le_R hx
  have hVN := hVR.trans h.R_le_normalizer_K
  have hσ : P.pf a ∈ P.im (conjSubgroup (blockU K) x) := by
    rw [h.im_conj_eq P hR hx hx1, ← hE]
    exact (P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩
  obtain ⟨v, hv, hva⟩ := (P.mem_im_pf hVN).1 hσ
  have hp : v⁻¹ * a ∈ pCoreOf 2 H := by
    have hπ : P.pf (v⁻¹ * a) = 1 := by
      rw [P.pf_mul (inv_mem (hVN hv)) (hAN ha), P.pf_inv (hVN hv), hva, inv_mul_cancel]
    have hm : v⁻¹ * a ∈ Subgroup.normalizer (K : Set G) := mul_mem (inv_mem (hVN hv)) (hAN ha)
    rw [P.pf_eq hm] at hπ
    have hc := (P.hker _).1 hπ
    rw [← h.R_inf_centralizer_eq]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hVR hv)) (hAR ha),
      Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have := hc u hu
    calc u * (v⁻¹ * a) = ((v⁻¹ * a) * u * (v⁻¹ * a)⁻¹) * (v⁻¹ * a) := by rw [this]
      _ = (v⁻¹ * a) * u := by group
  rw [h.pCoreOf_eq_sup h5] at hp
  have hUK : blockU K ≤ K := (C1.blockU_le_blockQ h.short).trans (C1.blockQ_le K)
  obtain ⟨u, hu, d, hd, hud⟩ := C5.mem_sup_of_commute (A := blockU K)
    (B := R ⊓ Subgroup.centralizer (K : Set G))
    (fun u hu d hd => Subgroup.mem_centralizer_iff.mp hd.2 u (hUK hu)) hp
  exact ⟨v, hv, u, hu, d, hd, by rw [← hud]; group⟩

theorem eq_conj_of_im (h5 : IsAltType K 5) (P : A5Pi K) (hR : P.im R = Dstd) {x : G}
    (hx : x ∈ M₀) (hx1 : ¬ conjSubgroup (blockU K) x ≤ pCoreOf 2 H) {A : Subgroup G}
    (hA : IsMaxElemAbelian R A) (hE : P.im A = Estd) : A = conjSubgroup (pCoreOf 2 H) x := by
  classical
  set U := blockU K with hU
  set V := conjSubgroup U x with hV
  set D := R ⊓ Subgroup.centralizer (K : Set G) with hD
  have hQmax := h.isMaxElemAbelian h5 P hR hx hx1
  have hQe := C5.isElemAbelian_two_iff.mp hQmax.2.1
  have hAe := C5.isElemAbelian_two_iff.mp hA.2.1
  have hVe := C5.isElemAbelian_two_iff.mp (h.conj_elem x)
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := hA.1.trans h.R_le_normalizer_K
  have hVR : V ≤ R := h.conj_le_R hx
  have hVN : V ≤ Subgroup.normalizer (K : Set G) := hVR.trans h.R_le_normalizer_K
  have hUK : U ≤ K := (C1.blockU_le_blockQ h.short).trans (C1.blockQ_le K)
  have hDQ : D ≤ pCoreOf 2 H := by rw [h.pCoreOf_eq_sup h5]; exact le_sup_right
  have hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d := fun d hd v hv =>
    h.comm_conj h5 P hR hx hx1 hd hv
  have hDU : ∀ d ∈ D, ∀ u ∈ U, d * u = u * d := fun d hd u hu =>
    (Subgroup.mem_centralizer_iff.mp hd.2 u (hUK hu)).symm
  have hdec := fun {a : G} (ha : a ∈ A) => h.exists_decomp h5 P hR hx hx1 hA.1 hE ha
  have hDA : D ≤ A := by
    have hcomm : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a := by
      intro a ha d hd
      obtain ⟨v, hv, u, hu, d', hd', rfl⟩ := hdec ha
      have h1 := hDV d hd v hv
      have h2 := hDU d hd u hu
      have h3 := hQe.1 d (hDQ hd) d' (hDQ hd')
      calc v * (u * d') * d = v * u * (d' * d) := by group
        _ = v * u * (d * d') := by rw [h3]
        _ = v * (u * d) * d' := by group
        _ = v * (d * u) * d' := by rw [h2]
        _ = (v * d) * u * d' := by group
        _ = (d * v) * u * d' := by rw [h1]
        _ = d * (v * (u * d')) := by group
    have hDe : IsElemAbelian 2 D := B2F.isElemAbelian_mono hDQ hQmax.2.1
    have hADe := B2F.isElemAbelian_sup_of_commute hA.2.1 hDe hcomm
    have hADR : A ⊔ D ≤ R := sup_le hA.1 inf_le_left
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ A ⊔ D) (hA.2.2 _ hADR hADe)
    rw [heq]
    exact le_sup_right
  have hCAV : U ⊓ Subgroup.centralizer (A : Set G) = U ⊓ Subgroup.centralizer (V : Set G) :=
    inf_centralizer_eq_of_im P hAN hVN (by rw [hE, h.im_conj_eq P hR hx hx1])
  obtain ⟨hW1, hW2, -⟩ := h.cent_conj P hR hx hx1
  have hkey : ∀ v ∈ V, ∀ u ∈ U, v * u ∈ A → u ∈ Subgroup.centralizer (V : Set G) := by
    intro v hv u hu hvu
    have hσV : P.pf v ∈ Estd := by
      rw [← h.im_conj_eq P hR hx hx1]; exact (P.mem_im_pf hVN).2 ⟨v, hv, rfl⟩
    by_cases hσ1 : P.pf v = 1
    · have hvU : v ∈ U := by
        have hvC : v ∈ V ⊓ Subgroup.centralizer (U : Set G) := by
          refine ⟨hv, Subgroup.mem_centralizer_iff.mpr fun u' hu' => ?_⟩
          have := (P.comm_iff (hVN hv) hu').2 (by rw [hσ1, vact_one])
          exact this.symm
        rw [← hW2] at hvC
        exact hvC.1
      have hb : v * u ∈ U ⊓ Subgroup.centralizer (A : Set G) :=
        ⟨mul_mem hvU hu, Subgroup.mem_centralizer_iff.mpr fun a ha => hAe.1 a ha _ hvu⟩
      rw [hCAV] at hb
      have hvW : v ∈ U ⊓ Subgroup.centralizer (V : Set G) := by rw [hW1]; exact ⟨hvU, hv⟩
      have : u = v⁻¹ * (v * u) := by group
      rw [this]
      exact mul_mem (inv_mem hvW.2) hb.2
    ·
      have hσE : P.pf v ∈ Eset := (mem_Estd _).1 hσV
      have hpE : partner (P.pf v) ∈ Estd := by
        rw [mem_Estd]
        unfold partner
        split_ifs
        · exact t2_mem_Eset
        · exact t1_mem_Eset
      rw [← hE] at hpE
      obtain ⟨a', ha', ha'σ⟩ := (P.mem_im_pf hAN).1 hpE
      obtain ⟨v', hv', u', hu', d', hd', rfl⟩ := hdec ha'
      have hb' : v' * u' ∈ A := by
        have := mul_mem ha' (inv_mem (hDA hd'))
        simpa [mul_assoc] using this
      have hUN : U ≤ Subgroup.normalizer (K : Set G) := hUK.trans Subgroup.le_normalizer
      have hDN : D ≤ Subgroup.normalizer (K : Set G) := inf_le_left.trans h.R_le_normalizer_K
      have hpfu : ∀ {u₀ : G}, u₀ ∈ U → P.pf u₀ = 1 := by
        intro u₀ hu₀
        rw [P.pf_eq (hUN hu₀), P.hker]
        intro u₁ hu₁
        rw [blockU_comm_blockU h.short hu₀ hu₁]
        group
      have hpfd : P.pf d' = 1 := by
        rw [P.pf_eq (hDN hd'), P.hker]
        intro u₁ hu₁
        rw [hDU d' hd' u₁ hu₁]
        group
      have hσ' : P.pf v' = partner (P.pf v) := by
        rw [← ha'σ, P.pf_mul (hVN hv') (mul_mem (hUN hu') (hDN hd')),
          P.pf_mul (hUN hu') (hDN hd'), hpfu hu', hpfd, one_mul, mul_one]
      have hcomm_of_sq : ∀ {v₀ u₀ : G}, v₀ ∈ V → u₀ ∈ U → v₀ * u₀ ∈ A → v₀ * u₀ = u₀ * v₀ := by
        intro v₀ u₀ hv₀ hu₀ hb₀
        have h1 : (v₀ * u₀) ^ 2 = 1 := hAe.2 _ hb₀
        have h2 : v₀ ^ 2 = 1 := hVe.2 _ hv₀
        have h3 : u₀ ^ 2 = 1 := C1.blockU_sq h.short u₀ hu₀
        have hv₀i : v₀⁻¹ = v₀ := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact h2
        have hu₀i : u₀⁻¹ = u₀ := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact h3
        have h4 : v₀ * u₀ = (v₀ * u₀)⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← pow_two]; exact h1
        rw [mul_inv_rev, hv₀i, hu₀i] at h4
        exact h4
      have hw := (P.comm_iff (hVN hv) hu).1 (hcomm_of_sq hv hu hvu)
      have hw' := (P.comm_iff (hVN hv') hu').1 (hcomm_of_sq hv' hu' hb')
      have hvv : v * v' = v' * v := hVe.1 v hv v' hv'
      have hrel := (P.comm_vu (hVN hv) (hVN hv') hu hu' hvv).1 (hAe.1 _ hvu _ hb')
      have hinv : ∀ σ ∈ Eset, σ⁻¹ = σ := fun σ hσ => by
        rw [inv_eq_iff_mul_eq_one]; exact Eset_sq σ hσ
      have hpE' : partner (P.pf v) ∈ Eset := by
        unfold partner
        split_ifs
        · exact t2_mem_Eset
        · exact t1_mem_Eset
      rw [hσ', hinv _ hpE', hinv _ hσE] at hrel
      rw [hσ'] at hw'
      have hfix := fin_comm (P.pf v) hσE hσ1 (P.bf u).1 (P.bf u').1
        (congrArg Subtype.val hw) (congrArg Subtype.val hw') (congrArg Subtype.val hrel)
      have hfixE := fixE_of _ hfix.1 hfix.2
      refine Subgroup.mem_centralizer_iff.mpr fun v₂ hv₂ => ?_
      have hσ₂ : P.pf v₂ ∈ Eset := by
        rw [← mem_Estd, ← h.im_conj_eq P hR hx hx1]; exact (P.mem_im_pf hVN).2 ⟨v₂, hv₂, rfl⟩
      exact (P.comm_iff (hVN hv₂) hu).2 (Subtype.ext (hfixE _ hσ₂))
  have hAV : A ≤ conjSubgroup (pCoreOf 2 H) x := by
    rw [h.conj_pCoreOf hx]
    intro a ha
    refine ⟨hA.1 ha, Subgroup.mem_centralizer_iff.mpr fun v₂ hv₂ => ?_⟩
    obtain ⟨v, hv, u, hu, d, hd, rfl⟩ := hdec ha
    have hb : v * u ∈ A := by
      have := mul_mem ha (inv_mem (hDA hd))
      simpa [mul_assoc] using this
    have hu2 := Subgroup.mem_centralizer_iff.mp (hkey v hv u hu hb) v₂ hv₂
    have h1 := hVe.1 v₂ hv₂ v hv
    have h3 := (hDV d hd v₂ hv₂).symm
    calc v₂ * (v * (u * d)) = (v₂ * v) * u * d := by group
      _ = (v * v₂) * u * d := by rw [h1]
      _ = v * (v₂ * u) * d := by group
      _ = v * (u * v₂) * d := by rw [hu2]
      _ = v * u * (v₂ * d) := by group
      _ = v * u * (d * v₂) := by rw [h3]
      _ = v * (u * d) * v₂ := by group
  have hQx : IsMaxElemAbelian R (conjSubgroup (pCoreOf 2 H) x) :=
    C56.isMaxElemAbelian_conjSubgroup hQmax (h.normal_R hx)
  exact Subgroup.eq_of_le_of_card_ge hAV (hA.2.2 _ hQx.1 hQx.2.1)

theorem relIndex_eq_two_of_alt5 (h5 : IsAltType K 5) :
    (M₀ ⊓ Subgroup.normalizer (K : Set G)).relIndex M₀ = 2 := by
  obtain ⟨P, -, hR⟩ := h.exists_std h5
  obtain ⟨x, hx, hx1⟩ := h.exists_conj_not_le
  have hQmax := h.isMaxElemAbelian h5 P hR hx hx1
  refine relIndex_eq_two h.maxN (fun g hg => h.mem_normalizer_pCoreOf hg) hx ?_ fun m hm => ?_
  · intro heq
    apply hx1
    have := C5.conjSubgroup_mono h.blockU_le_pCoreOf x
    rwa [heq] at this
  · have hm' := C56.isMaxElemAbelian_conjSubgroup hQmax (h.normal_R hm)
    have hRm : R ≤ Subgroup.normalizer (conjSubgroup (pCoreOf 2 H) m : Set G) :=
      C5.le_normalizer_conj (h.normal_R hm) h.R_le_normalizer_pCoreOf
    rcases h.im_cases P hR hm' hRm with h1 | h1
    · exact Or.inl (h.eq_pCoreOf_of_im P hQmax hm' h1)
    · exact Or.inr (h.eq_conj_of_im h5 P hR hx hx1 hm' h1)

end Setup

end CFSG.Quasithin.H13.Ch4.C57
