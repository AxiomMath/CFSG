module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open K22p

lemma smul_eq_of_mem_of_normal_isPGroup {q : ℕ} {M : Type} [Group M] (σ : MulAut M)
    {N : Subgroup M} [N.Normal] (hNpg : IsPGroup q N) (hfix : FixesSylow σ q) {n : M}
    (hn : n ∈ N) : σ n = n := by
  unfold FixesSylow at hfix
  obtain ⟨Q, hQ⟩ := hfix
  exact hQ n (IsPGroup.le_sylow_of_normal hNpg Q hn)

lemma le_center_of_commSub_eq_top {M : Type} [Group M] (σ : MulAut M)
    (hcomm : commSub σ = ⊤) {N : Subgroup M} [hNnormal : N.Normal]
    (hfixN : ∀ n ∈ N, σ n = n) : N ≤ Subgroup.center M := by
  have hle : commSub σ ≤ Subgroup.centralizer (N : Set M) := by
    unfold commSub
    rw [Subgroup.closure_le]
    rintro y ⟨x, rfl⟩
    change x⁻¹ * σ x ∈ Subgroup.centralizer (N : Set M)
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hconj : σ x * n * (σ x)⁻¹ = x * n * x⁻¹ := by
      have hmem : x * n * x⁻¹ ∈ N := hNnormal.conj_mem n hn x
      have h := hfixN (x * n * x⁻¹) hmem
      simpa only [map_mul, map_inv, hfixN n hn] using h
    have hkey : (x⁻¹ * σ x) * n * (x⁻¹ * σ x)⁻¹ = n := by
      calc (x⁻¹ * σ x) * n * (x⁻¹ * σ x)⁻¹
          = x⁻¹ * (σ x * n * (σ x)⁻¹) * x := by group
        _ = x⁻¹ * (x * n * x⁻¹) * x := by rw [hconj]
        _ = n := by group
    exact (mul_inv_eq_iff_eq_mul.mp hkey).symm
  have htop : (⊤ : Subgroup M) ≤ Subgroup.centralizer (N : Set M) := by
    rw [← hcomm]
    exact hle
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro m
  have hm : m ∈ Subgroup.centralizer (N : Set M) := htop (Subgroup.mem_top m)
  exact (Subgroup.mem_centralizer_iff.mp hm n hn).symm

lemma smul_mem_complement {q : ℕ} (hq : q.Prime) {M : Type} [Group M] [Finite M]
    (σ : MulAut M) {N C : Subgroup M} (hqind : ¬ q ∣ N.index) (hNpg : IsPGroup q N)
    (hcenter : N ≤ Subgroup.center M) (hfixN : ∀ n ∈ N, σ n = n)
    (hC : Subgroup.IsComplement' N C) : ∀ c ∈ C, σ c ∈ C := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcardC : Nat.card C = N.index := hC.card_right
  have hqC : ∀ x ∈ C, ¬ q ∣ orderOf (x : M) := by
    intro x hx
    have hdvd : orderOf (x : M) ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hx
    rw [hcardC] at hdvd
    exact fun hdiv => hqind (hdiv.trans hdvd)
  intro c hc
  obtain ⟨⟨n, c'⟩, hnc, -⟩ := hC.existsUnique (σ (c : M))
  have hcomm : Commute (n : M) (c' : M) :=
    (Subgroup.mem_center_iff.mp (hcenter n.property) (c' : M)).symm
  have hcopOrd : Nat.Coprime (orderOf (n : M)) (orderOf (c' : M)) := by
    obtain ⟨k, hk⟩ := hNpg.exists_orderOf_dvd_pow n
    rw [← Subgroup.orderOf_coe (n : N)] at hk
    exact Nat.Coprime.of_dvd_left hk
      ((hq.coprime_iff_not_dvd.mpr (hqC (c' : M) c'.property)).pow_left k)
  have horder : orderOf ((n : M) * (c' : M)) =
      orderOf (n : M) * orderOf (c' : M) :=
    hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcopOrd
  have hqord : ¬ q ∣ orderOf ((n : M) * (c' : M)) := by
    rw [hnc, MulEquiv.orderOf_eq]
    exact hqC (c : M) hc
  have hqordn : ¬ q ∣ orderOf (n : M) := by
    intro hdiv
    exact hqord (by rw [horder]; exact dvd_mul_of_dvd_left hdiv _)
  have hnM : (n : M) = 1 := by
    by_contra hne
    have hn_ne : (n : N) ≠ 1 := fun h => hne (congrArg Subtype.val h)
    have hthis : q ∣ orderOf (n : N) := hNpg.dvd_orderOf hn_ne
    rw [← Subgroup.orderOf_coe (n : N)] at hthis
    exact hqordn hthis
  rw [← hnc, hnM, one_mul]
  exact c'.property

lemma commSub_le_complement {M : Type} [Group M] (σ : MulAut M) {N C : Subgroup M}
    (hfixN : ∀ n ∈ N, σ n = n) (hC : Subgroup.IsComplement' N C)
    (hCinv : ∀ c ∈ C, σ c ∈ C) : commSub σ ≤ C := by
  unfold commSub
  rw [Subgroup.closure_le]
  rintro y ⟨x, rfl⟩
  change x⁻¹ * σ x ∈ C
  obtain ⟨⟨n, c⟩, hnc, -⟩ := hC.existsUnique x
  have hxinv : x⁻¹ * σ x = (c : M)⁻¹ * σ (c : M) := by
    rw [← hnc, map_mul, hfixN (n : M) n.property]
    group
  rw [hxinv]
  exact C.mul_mem (C.inv_mem c.property) (hCinv (c : M) c.property)

theorem chiefAb_holds : K22p.ChiefAb := by
  intro q hq M _ _ σ hcomm N hNnormal hNpg hqind hfix
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : N.Normal := hNnormal
  have hfixN : ∀ n ∈ N, σ n = n :=
    fun n hn => smul_eq_of_mem_of_normal_isPGroup σ hNpg hfix hn
  have hcenter : N ≤ Subgroup.center M :=
    le_center_of_commSub_eq_top σ hcomm hfixN
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    obtain ⟨k, hk⟩ := hNpg.exists_card_eq
    rw [hk]
    exact (hq.coprime_iff_not_dvd.mpr hqind).pow_left k
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := N) hcop
  have hCinv : ∀ c ∈ C, σ c ∈ C :=
    smul_mem_complement hq σ hqind hNpg hcenter hfixN hC
  have hle : commSub σ ≤ C := commSub_le_complement σ hfixN hC hCinv
  have hCtop : C = ⊤ := top_le_iff.mp (hcomm ▸ hle)
  calc N = N ⊓ ⊤ := (inf_top_eq N).symm
    _ = N ⊓ C := by rw [hCtop]
    _ = ⊥ := hC.disjoint.eq_bot

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
