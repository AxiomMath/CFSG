module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront13
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Layer13
import CFSG.Quasithin.Vol2.Ch11SecA12Cop
import CFSG.Quasithin.EmptyFaithful.S1469Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F13 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s13b_pCoreOf_le (M : Subgroup G) : CFSG.Open.pCoreOf 2 M ≤ M :=
  Subgroup.map_subtype_le _

theorem uc22s13b_isPGroup_pCoreOf (M : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
  CFSG.pCore_isPGroup.map M.subtype

theorem uc22s13b_le_normalizer_pCoreOf (M : Subgroup G) :
    M ≤ normalizer (CFSG.Open.pCoreOf 2 M : Set G) := by
  have hsub : (CFSG.Open.pCoreOf 2 M).subgroupOf M = CFSG.pCore 2 ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hnorm : ((CFSG.Open.pCoreOf 2 M).subgroupOf M).Normal := by
    rw [hsub]
    exact CFSG.pCore_normal
  exact (normal_subgroupOf_iff_le_normalizer (uc22s13b_pCoreOf_le M)).1 hnorm

theorem uc22s13b_mem_pCoreOf_iff {M : Subgroup G} {x : G} (hx : x ∈ M) :
    x ∈ CFSG.Open.pCoreOf 2 M ↔
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ : Bar2 M) = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem uc22s13b_commutator_mem {M : Subgroup G} {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (h : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩ : Bar2 M) *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) :
    a * b * a⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  have hab : a * b * a⁻¹ * b⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  rw [uc22s13b_mem_pCoreOf_iff hab]
  have he : (⟨a * b * a⁻¹ * b⁻¹, hab⟩ : ↥M) =
      ⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥M)⁻¹ * (⟨b, hb⟩ : ↥M)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

theorem uc22s13b_mk_mem_barImage {M X : Subgroup G} {x : G} (hx : x ∈ M) (hxX : x ∈ X) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ : Bar2 M) ∈ barImage M X :=
  ⟨⟨x, hx⟩, hxX, rfl⟩

theorem uc22s13b_mem_cMStar {M X : Subgroup G} {x : G} (hx : x ∈ M)
    (h : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ : Bar2 M) ∈
      centralizer (barImage M X : Set (Bar2 M))) : x ∈ cMStar M X :=
  ⟨⟨x, hx⟩, h, rfl⟩

theorem uc22s13b_of_mem_cMStar {M X : Subgroup G} {x : G} (h : x ∈ cMStar M X) :
    ∃ hx : x ∈ M, (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩ : Bar2 M) ∈
      centralizer (barImage M X : Set (Bar2 M)) := by
  obtain ⟨x', hx', rfl⟩ := h
  exact ⟨x'.2, hx'⟩

theorem uc22s13b_conj_mem_cMStar {M X : Subgroup G} (hXM : X ≤ M) (hXn : (X.subgroupOf M).Normal)
    {m c : G} (hm : m ∈ M) (hc : c ∈ cMStar M X) : m * c * m⁻¹ ∈ cMStar M X := by
  haveI : (barImage M X).Normal :=
    hXn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (QuotientGroup.mk'_surjective _)
  obtain ⟨hcM, hcC⟩ := uc22s13b_of_mem_cMStar hc
  have hmem : m * c * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm)
  refine uc22s13b_mem_cMStar hmem ?_
  have he : (⟨m * c * m⁻¹, hmem⟩ : ↥M) = ⟨m, hm⟩ * ⟨c, hcM⟩ * (⟨m, hm⟩ : ↥M)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv]
  exact (normal_centralizer (H := barImage M X)).conj_mem _ hcC _

theorem uc22s13b_mem_sup_cMStar {M K : Subgroup G} (hKn : (K.subgroupOf M).Normal) {y : G}
    (hy : y ∈ M)
    (h : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩ : Bar2 M) ∈
      barImage M K ⊔ centralizer (barImage M K : Set (Bar2 M))) :
    y ∈ K ⊔ cMStar M K := by
  haveI : (barImage M K).Normal :=
    hKn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (QuotientGroup.mk'_surjective _)
  obtain ⟨j, hj, c, hc, hjc⟩ := mem_sup_of_normal_left.1 h
  obtain ⟨k, hk, rfl⟩ := hj
  have hkyM : (k : G)⁻¹ * y ∈ M := M.mul_mem (M.inv_mem k.2) hy
  have hkc : (k : G)⁻¹ * y ∈ cMStar M K := by
    refine uc22s13b_mem_cMStar hkyM ?_
    have he : (⟨(k : G)⁻¹ * y, hkyM⟩ : ↥M) = k⁻¹ * ⟨y, hy⟩ := rfl
    rw [he, map_mul, map_inv, ← hjc, inv_mul_cancel_left]
    exact hc
  have hyk : y = (k : G) * ((k : G)⁻¹ * y) := by group
  rw [hyk]
  exact mul_mem_sup hk hkc

theorem uc22s13b_mem_sup_cMStar_of_inner {M K : Subgroup G} (hKn : (K.subgroupOf M).Normal)
    {y : G} (hy : y ∈ M)
    (h : ∃ j ∈ barImage M K, ∀ k ∈ barImage M K,
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩ : Bar2 M) * k *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩)⁻¹ = j * k * j⁻¹) :
    y ∈ K ⊔ cMStar M K := by
  obtain ⟨j, hj, hjk⟩ := h
  refine uc22s13b_mem_sup_cMStar hKn hy ?_
  set u : Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩
  have hc : j⁻¹ * u ∈ centralizer (barImage M K : Set (Bar2 M)) := by
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := hjk k hk
    have h2 : j⁻¹ * u * k * (j⁻¹ * u)⁻¹ = k := by
      calc j⁻¹ * u * k * (j⁻¹ * u)⁻¹ = j⁻¹ * (u * k * u⁻¹) * j := by group
        _ = k := by rw [h1]; group
    calc k * (j⁻¹ * u) = j⁻¹ * u * k * (j⁻¹ * u)⁻¹ * (j⁻¹ * u) := by rw [h2]
      _ = j⁻¹ * u * k := by group
  have hu : u = j * (j⁻¹ * u) := by group
  rw [hu]
  exact mul_mem_sup hj hc

theorem uc22s13b_commutator_le {M K : Subgroup G} (hKn : (K.subgroupOf M).Normal)
    (hOut : ∀ σ τ : MulAut ↥(barImage M K), ∃ y : ↥(barImage M K),
      σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y) :
    ⁅M, M⁆ ≤ K ⊔ cMStar M K := by
  haveI : (barImage M K).Normal :=
    hKn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (QuotientGroup.mk'_surjective _)
  have hQ := PartTwo.s13_commutator_le_sup_centralizer (barImage M K) hOut
  rw [commutator_le]
  intro a ha b hb
  have hab : ⁅a, b⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  refine uc22s13b_mem_sup_cMStar hKn hab (hQ ?_)
  have he : (⟨⁅a, b⁆, hab⟩ : ↥M) = ⁅(⟨a, ha⟩ : ↥M), ⟨b, hb⟩⁆ := rfl
  rw [he, map_commutatorElement, commutator_def]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

theorem uc22s13b_le_normalizer_of_commutator_le {M N : Subgroup G} (hMN : ⁅M, M⁆ ≤ N)
    (hNM : N ≤ M) : M ≤ normalizer (N : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have h1 : m * n * m⁻¹ = ⁅m, n⁆ * n := by rw [commutatorElement_def]; group
    rw [h1]
    exact N.mul_mem (hMN (commutator_mem_commutator hm (hNM hn))) hn
  · intro hn
    have h1 : n = ⁅m⁻¹, m * n * m⁻¹⁆ * (m * n * m⁻¹) := by rw [commutatorElement_def]; group
    rw [h1]
    exact N.mul_mem (hMN (commutator_mem_commutator (M.inv_mem hm) (hNM hn))) hn

theorem uc22s13b_exists_cent {M A B : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : IsPGroup p A) (hBM : B ≤ M) (hAB : A ≤ normalizer (B : Set G))
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 M) {b : G} (hb : b ∈ B) :
    ∃ c ∈ B ⊓ centralizer (A : Set G), c⁻¹ * b ∈ CFSG.Open.pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 M
  have hO2 : IsPGroup 2 ↥(B ⊓ O) := (uc22s13b_isPGroup_pCoreOf M).to_le inf_le_right
  have hcop : Nat.Coprime p (Nat.card ↥(B ⊓ O)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hO2
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hBN : B ≤ normalizer ((B ⊓ O : Subgroup G) : Set G) := by
    intro x hx
    have hxO := mem_normalizer_iff.1 (uc22s13b_le_normalizer_pCoreOf M (hBM hx))
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyB, hyO⟩
      exact ⟨B.mul_mem (B.mul_mem hx hyB) (B.inv_mem hx), (hxO y).1 hyO⟩
    · rintro ⟨hyB, hyO⟩
      refine ⟨?_, (hxO y).2 hyO⟩
      have h1 := B.mul_mem (B.mul_mem (B.inv_mem hx) hyB) hx
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h1
  have hc' : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ B ⊓ O := by
    intro a ha b hb
    refine ⟨B.mul_mem ((mem_normalizer_iff.1 (hAB ha) b).1 hb) (B.inv_mem hb), hc a ha b hb⟩
  obtain ⟨c, hcmem, hcb⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.exists_mem_centralizer_of_coprime hp hA
    hAB inf_le_left hBN hcop hc' hb
  exact ⟨c, hcmem, hcb.2⟩

theorem uc22s13b_le_commutator_sup {M L C : Subgroup G} (hLM : L ≤ M) (hCM : C ≤ M)
    (hLperf : ⁅L, L⁆ = L) (hdec : ∀ l ∈ L, ∃ c ∈ C, c⁻¹ * l ∈ CFSG.Open.pCoreOf 2 M) :
    L ≤ ⁅C, C⁆ ⊔ CFSG.Open.pCoreOf 2 M := by
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hbar : ∀ l (hl : l ∈ L), ∃ c ∈ C, ∃ hcM : c ∈ M, π ⟨l, hLM hl⟩ = π ⟨c, hcM⟩ := by
    intro l hl
    obtain ⟨c, hc, hcl⟩ := hdec l hl
    refine ⟨c, hc, hCM hc, ?_⟩
    have hmem : c⁻¹ * l ∈ M := M.mul_mem (M.inv_mem (hCM hc)) (hLM hl)
    have h1 := (uc22s13b_mem_pCoreOf_iff hmem).1 hcl
    have he : (⟨c⁻¹ * l, hmem⟩ : ↥M) = (⟨c, hCM hc⟩ : ↥M)⁻¹ * ⟨l, hLM hl⟩ := rfl
    rw [he, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  calc L = ⁅L, L⁆ := hLperf.symm
    _ ≤ ⁅C, C⁆ ⊔ CFSG.Open.pCoreOf 2 M := by
      rw [commutator_le]
      intro l₁ hl₁ l₂ hl₂
      obtain ⟨c₁, hc₁, hc₁M, e₁⟩ := hbar l₁ hl₁
      obtain ⟨c₂, hc₂, hc₂M, e₂⟩ := hbar l₂ hl₂
      have hcomm : ∀ {a b : G}, a ∈ M → b ∈ M → ⁅a, b⁆ ∈ M := fun ha hb => by
        rw [commutatorElement_def]
        exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
      have hmem : ⁅c₁, c₂⁆⁻¹ * ⁅l₁, l₂⁆ ∈ M :=
        M.mul_mem (M.inv_mem (hcomm hc₁M hc₂M)) (hcomm (hLM hl₁) (hLM hl₂))
      have hkey : ⁅c₁, c₂⁆⁻¹ * ⁅l₁, l₂⁆ ∈ CFSG.Open.pCoreOf 2 M := by
        rw [uc22s13b_mem_pCoreOf_iff hmem]
        have he : (⟨⁅c₁, c₂⁆⁻¹ * ⁅l₁, l₂⁆, hmem⟩ : ↥M) =
            ⁅(⟨c₁, hc₁M⟩ : ↥M), ⟨c₂, hc₂M⟩⁆⁻¹ * ⁅(⟨l₁, hLM hl₁⟩ : ↥M), ⟨l₂, hLM hl₂⟩⁆ := rfl
        change π _ = 1
        rw [he, map_mul, map_inv, map_commutatorElement, map_commutatorElement, e₁, e₂,
          inv_mul_cancel]
      have hl : ⁅l₁, l₂⁆ = ⁅c₁, c₂⁆ * (⁅c₁, c₂⁆⁻¹ * ⁅l₁, l₂⁆) := by group
      rw [hl]
      exact mul_mem_sup (commutator_mem_commutator hc₁ hc₂) hkey

theorem uc22s13b_mem_of_odd {M L N A : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) (hLperf : ⁅L, L⁆ = L) (hA : IsPGroup p A)
    (hAM : A ≤ M) (hAL : A ≤ cMStar M L) {g : G}
    (hcent : L ⊓ centralizer (A : Set G) ≤ M.map (MulAut.conj g⁻¹).toMonoidHom)
    (hNM : N ≤ M) (hMN : ⁅M, M⁆ ≤ N) {y : G} (hyM : y ∈ M)
    (hyL : y ∈ L.map (MulAut.conj g).toMonoidHom) (hy : Odd (orderOf y)) : y ∈ N := by
  set O := CFSG.Open.pCoreOf 2 M
  set C := L ⊓ centralizer (A : Set G)
  have hMnL : M ≤ normalizer (L : Set G) := (normal_subgroupOf_iff_le_normalizer hLM).1 hLn
  have hdec : ∀ l ∈ L, ∃ c ∈ C, c⁻¹ * l ∈ O := by
    intro l hl
    refine uc22s13b_exists_cent hp hp2 hA hLM (hAM.trans hMnL) (fun a ha b hb => ?_) hl
    obtain ⟨haM, haC⟩ := uc22s13b_of_mem_cMStar (hAL ha)
    exact uc22s13b_commutator_mem haM (hLM hb)
      ((mem_centralizer_iff.1 haC _ (uc22s13b_mk_mem_barImage (hLM hb) hb)).symm)
  have hLC : L ≤ ⁅C, C⁆ ⊔ O := uc22s13b_le_commutator_sup hLM (inf_le_left.trans hLM) hLperf hdec
  have hCC : ⁅C, C⁆ ≤ M := by
    rw [commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)
    exact hLM hab.1
  obtain ⟨x, hxL, hxy⟩ := hyL
  have hx : x ∈ ((⁅C, C⁆ ⊔ O : Subgroup G) : Set G) := hLC hxL
  rw [coe_mul_of_left_le_normalizer_right _ _ (hCC.trans (uc22s13b_le_normalizer_pCoreOf M))]
    at hx
  obtain ⟨c, hc, u, hu, hcu⟩ := hx
  have hCg : C.map (MulAut.conj g).toMonoidHom ≤ M := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨m, hm, hmd⟩ := hcent hd
    have hdm : (MulAut.conj g).toMonoidHom d = m := by
      rw [← hmd]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hdm]
    exact hm
  have hc' : (MulAut.conj g).toMonoidHom c ∈ N := by
    apply hMN
    have h1 : (MulAut.conj g).toMonoidHom c ∈ (⁅C, C⁆).map (MulAut.conj g).toMonoidHom :=
      mem_map_of_mem _ hc
    rw [map_commutator] at h1
    exact commutator_mono hCg hCg h1
  have hy' : y = (MulAut.conj g).toMonoidHom c * (MulAut.conj g).toMonoidHom u := by
    rw [← hxy, ← hcu, map_mul]
  have hu'M : (MulAut.conj g).toMonoidHom u ∈ M := by
    have h1 : (MulAut.conj g).toMonoidHom u = ((MulAut.conj g).toMonoidHom c)⁻¹ * y := by
      rw [hy']
      group
    rw [h1]
    exact M.mul_mem (M.inv_mem (hNM hc')) hyM
  have hQ : IsPGroup 2 ↥(O.map (MulAut.conj g).toMonoidHom ⊓ M) :=
    ((uc22s13b_isPGroup_pCoreOf M).map _).to_le inf_le_left
  have hQN : O.map (MulAut.conj g).toMonoidHom ⊓ M ≤ normalizer (N : Set G) :=
    inf_le_right.trans (uc22s13b_le_normalizer_of_commutator_le hMN hNM)
  have hmem : y ∈ N ⊔ (O.map (MulAut.conj g).toMonoidHom ⊓ M) := by
    rw [hy']
    exact mul_mem_sup hc' ⟨mem_map_of_mem _ hu, hu'M⟩
  exact CFSG.Quasithin.mem_of_odd_orderOf_of_sup_pGroup hQ hQN hmem hy

end CFSG.LocalAnalysis.UniquenessCase.UC22
