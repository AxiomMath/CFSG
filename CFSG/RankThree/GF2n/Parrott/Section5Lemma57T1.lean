module

public import CFSG.RankThree.GF2n.Parrott.Section5ConjugateZPowers
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Count

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem z_mem_centerIn_of_le_H (hz : orderOf z = 2) {K T : Subgroup G} (hK : K ≤ H z)
    (hzK : z ∈ K) (hT : IsSylowOf 2 T K) : z ∈ centerIn T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : K ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hK hc
  have hzT : z ∈ T :=
    le_isSylowOf_of_isPGroup_of_le_normalizer hT (Subgroup.zpowers_le.mpr hzK) hCN
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]))
      (Subgroup.mem_zpowers z)
  refine ⟨hzT, ?_⟩
  change z ∈ Subgroup.centralizer (T : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact Subgroup.mem_centralizer_singleton_iff.mp (hK (hT.le hs))

private theorem z_mem_centerIn_of_isSylowOf (h : Tim79a.ParrottHyp z) {σ : G}
    (hσH : σ ∈ H z) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ Subgroup.centralizer ({σ} : Set G))) :
    z ∈ centerIn T :=
  z_mem_centerIn_of_le_H h.1 inf_le_left
    (Subgroup.mem_inf.mpr ⟨z_mem_H, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hσH).symm⟩) hT

private lemma z_mem_centerIn_of_isSylowOf_normalizer (h : Tim79a.ParrottHyp z) {σ₁ : G}
    (hσ₁H : σ₁ ∈ H z) {S₀ : Subgroup G}
    (hS₀ : IsSylowOf 2 S₀ (H z ⊓ Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G))) :
    z ∈ centerIn S₀ := by
  have hzσ : z * σ₁ = σ₁ * z := (Subgroup.mem_centralizer_singleton_iff.mp hσ₁H).symm
  have hzN : z ∈ Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G) :=
    mem_normalizer_zpowers_iff.mpr (by
      rw [show z * σ₁ * z⁻¹ = σ₁ by rw [hzσ]; group]
      exact Subgroup.mem_zpowers σ₁)
  exact z_mem_centerIn_of_le_H h.1 inf_le_left
    (Subgroup.mem_inf.mpr ⟨z_mem_H, hzN⟩) hS₀

private lemma normalizer_inf_normalizer_zpowers_le_H {σ₁ : G} {S₀ : Subgroup G}
    (hzZ : z ∈ centerIn S₀)
    (hZS₀ : ∀ e ∈ centerIn S₀, IsConj z e → e = z) :
    Subgroup.normalizer (S₀ : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G) ≤ H z := by
  intro n hn
  have hnS : n * z * n⁻¹ ∈ S₀ := (Subgroup.mem_normalizer_iff.mp hn.1 z).mp hzZ.1
  have hzc : n * z * n⁻¹ ∈ centerIn S₀ := by
    refine ⟨hnS, ?_⟩
    change n * z * n⁻¹ ∈ Subgroup.centralizer (S₀ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S₀ := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn.1) s).mp hs
    have hcomm := Subgroup.mem_centralizer_iff.mp hzZ.2 (n⁻¹ * s * n) hs'
    calc s * (n * z * n⁻¹) = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * z * n⁻¹) * s := by group
  have heq : n * z * n⁻¹ = z := hZS₀ _ hzc (isConj_iff.mpr ⟨n, rfl⟩)
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc n * z = (n * z * n⁻¹) * n := by group
    _ = z * n := by rw [heq]

private lemma isSylowOf_inf_centralizer {σ₁ : G} {S₀ : Subgroup G}
    (hS₀ : IsSylowOf 2 S₀ (Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G))) :
    IsSylowOf 2 (S₀ ⊓ centralizer ({σ₁} : Set G)) (centralizer ({σ₁} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcz : Subgroup.centralizer ({σ₁} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers σ₁ : Set G) :=
    (CFSG.centralizer_zpowers_eq_centralizer_singleton σ₁).symm
  have hNK : Subgroup.centralizer ({σ₁} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G) := by
    intro x hx
    rw [mem_normalizer_zpowers_iff]
    rw [show x * σ₁ * x⁻¹ = σ₁ by rw [Subgroup.mem_centralizer_singleton_iff.mp hx]; group]
    exact Subgroup.mem_zpowers σ₁
  have hKN : Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer ({σ₁} : Set G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
    have hn' : (Subgroup.zpowers σ₁).map (MulEquiv.toMonoidHom (MulAut.conj n)) =
        Subgroup.zpowers σ₁ := hn
    rw [hcz]
    show (Subgroup.centralizer (Subgroup.zpowers σ₁ : Set G)).map
        (MulEquiv.toMonoidHom (MulAut.conj n)) =
      Subgroup.centralizer (Subgroup.zpowers σ₁ : Set G)
    rw [← centralizer_map_conj n (Subgroup.zpowers σ₁), hn']
  exact IsSylowOf.inf_of_le_normalizer hS₀ hNK hKN

private lemma inf_centralizer_eq_of_isSylowOf {σ₁ : G} {T₁ S₀ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ centralizer ({σ₁} : Set G))) (hTS : T₁ ≤ S₀) (hSle : S₀ ≤ H z)
    (hSinf : IsSylowOf 2 (S₀ ⊓ centralizer ({σ₁} : Set G)) (centralizer ({σ₁} : Set G))) :
    S₀ ⊓ centralizer ({σ₁} : Set G) = T₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsSylowOf.eq_of_le hT₁ ?_ ?_ ?_
  · exact le_inf hTS (hT₁.le.trans inf_le_right)
  · exact le_inf (inf_le_left.trans hSle) inf_le_right
  · exact hSinf.isPGroup

theorem isSylowOf_centralizer_of_centerIn_normalizer (h : Tim79a.ParrottHyp z) {σ₁ : G}
    (hσ₁H : σ₁ ∈ H z) {T₁ S₀ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ centralizer ({σ₁} : Set G)))
    (hS₀ : IsSylowOf 2 S₀ (H z ⊓ normalizer (zpowers σ₁ : Set G))) (hTS : T₁ ≤ S₀)
    (hZS₀ : ∀ e ∈ centerIn S₀, IsConj z e → e = z) :
    IsSylowOf 2 T₁ (centralizer ({σ₁} : Set G)) := by
  have hzZ : z ∈ centerIn S₀ := z_mem_centerIn_of_isSylowOf_normalizer h hσ₁H hS₀
  have hNle := normalizer_inf_normalizer_zpowers_le_H (σ₁ := σ₁) hzZ hZS₀
  have hS₀' : IsSylowOf 2 S₀ (Subgroup.normalizer (Subgroup.zpowers σ₁ : Set G)) :=
    isSylowOf_of_normalizer_inf_le hS₀ hNle
  have hSinf := isSylowOf_inf_centralizer (σ₁ := σ₁) hS₀'
  have hSeq := inf_centralizer_eq_of_isSylowOf hT₁ hTS (hS₀.le.trans inf_le_left) hSinf
  rw [← hSeq]
  exact hSinf

private lemma exists_conj_normalizer_subgroupOf {σ₁ : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({σ₁} : Set G))) {t z c : G}
    (htC : t ∈ centralizer ({σ₁} : Set G)) (hzC : z ∈ centralizer ({σ₁} : Set G))
    (hcC : c ∈ centralizer ({σ₁} : Set G)) (hc : c * t * c⁻¹ = z)
    (htZ : ∀ x ∈ T, x * t = t * x) (hzZ : ∀ x ∈ T, x * z = z * x) :
    ∃ n : ↥(centralizer ({σ₁} : Set G)),
      n ∈ Subgroup.normalizer ((T.subgroupOf (centralizer ({σ₁} : Set G)) :
          Subgroup ↥(centralizer ({σ₁} : Set G))) : Set ↥(centralizer ({σ₁} : Set G))) ∧
      n⁻¹ * (⟨t, htC⟩ : ↥(centralizer ({σ₁} : Set G))) * n = ⟨z, hzC⟩ := by
  let C : Subgroup G := centralizer ({σ₁} : Set G)
  have : Finite ↥C := Subtype.finite
  have : Finite (Subgroup ↥C) :=
    Finite.of_injective (fun H : Subgroup ↥C => (H : Set ↥C)) SetLike.coe_injective
  have : Finite (Sylow 2 ↥C) :=
    Finite.of_injective (fun P : Sylow 2 ↥C => (P : Subgroup ↥C))
      (fun P Q h => Sylow.ext h)
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  have hQmem : ∀ (x : G) (hx : x ∈ T), (⟨x, hT.le hx⟩ : C) ∈ (Q : Subgroup ↥C) := by
    intro x hx
    rw [hQ]
    exact Subgroup.mem_subgroupOf.mpr hx
  have hxQ : (⟨t, htC⟩ : C) ∈ Subgroup.centralizer ((Q : Subgroup ↥C) : Set ↥C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hq' := hq
    rw [hQ] at hq'
    exact htZ (q : G) (Subgroup.mem_subgroupOf.mp hq')
  have hyQ : (⟨z, hzC⟩ : C) ∈ Subgroup.centralizer ((Q : Subgroup ↥C) : Set ↥C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hq' := hq
    rw [hQ] at hq'
    exact hzZ (q : G) (Subgroup.mem_subgroupOf.mp hq')
  have hgxy : (⟨c, hcC⟩ : C) * ⟨t, htC⟩ * (⟨c, hcC⟩ : C)⁻¹ = ⟨z, hzC⟩ := by
    apply Subtype.ext
    simpa using hc
  have hy' : (⟨c, hcC⟩ : C)⁻¹⁻¹ * (⟨t, htC⟩ : C) * (⟨c, hcC⟩ : C)⁻¹ ∈
      Subgroup.centralizer ((Q : Subgroup ↥C) : Set ↥C) := by
    rw [inv_inv]
    rwa [hgxy.symm] at hyQ
  obtain ⟨n, hnN, hneq⟩ :=
    Sylow.conj_eq_normalizer_conj_of_mem_centralizer Q (⟨t, htC⟩ : C) (⟨c, hcC⟩ : C)⁻¹ hxQ hy'
  have hn_t : n⁻¹ * (⟨t, htC⟩ : C) * n = ⟨z, hzC⟩ := by
    rw [← hneq, inv_inv]
    exact hgxy
  exact ⟨n, hQ ▸ hnN, hn_t⟩

omit [Finite G] in
private lemma mem_normalizer_of_mem_normalizer_subgroupOf {σ₁ : G} {T : Subgroup G}
    (hT : T ≤ centralizer ({σ₁} : Set G)) {n : ↥(centralizer ({σ₁} : Set G))}
    (hn : n ∈ Subgroup.normalizer ((T.subgroupOf (centralizer ({σ₁} : Set G)) :
        Subgroup ↥(centralizer ({σ₁} : Set G))) : Set ↥(centralizer ({σ₁} : Set G)))) :
    n.1 ∈ Subgroup.normalizer (T : Set G) := by
  let C : Subgroup G := centralizer ({σ₁} : Set G)
  have hfwd : ∀ x ∈ T, n.1 * x * n.1⁻¹ ∈ T := by
    intro x hx
    have hx' : (⟨x, hT hx⟩ : C) ∈ (T.subgroupOf C : Subgroup ↥C) :=
      Subgroup.mem_subgroupOf.mpr hx
    have hconj : n * ⟨x, hT hx⟩ * n⁻¹ ∈ (T.subgroupOf C : Subgroup ↥C) :=
      (Subgroup.mem_normalizer_iff.mp hn _).mp hx'
    have := Subgroup.mem_subgroupOf.mp hconj
    simpa using this
  have hbwd : ∀ x ∈ T, n.1⁻¹ * x * n.1 ∈ T := by
    intro x hx
    have hx' : (⟨x, hT hx⟩ : C) ∈ (T.subgroupOf C : Subgroup ↥C) :=
      Subgroup.mem_subgroupOf.mpr hx
    have hinv : n⁻¹ ∈ Subgroup.normalizer ((T.subgroupOf C : Subgroup ↥C) : Set ↥C) :=
      Subgroup.inv_mem _ hn
    have hconj : n⁻¹ * ⟨x, hT hx⟩ * n ∈ (T.subgroupOf C : Subgroup ↥C) := by
      simpa using (Subgroup.mem_normalizer_iff.mp hinv _).mp hx'
    have := Subgroup.mem_subgroupOf.mp hconj
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => by simpa using hfwd x hx, fun hx => ?_⟩
  have hx' : n.1 * x * n.1⁻¹ ∈ T := by simpa using hx
  have h2 : n.1⁻¹ * (n.1 * x * n.1⁻¹) * n.1 ∈ T := hbwd _ hx'
  rwa [show n.1⁻¹ * (n.1 * x * n.1⁻¹) * n.1 = x by group] at h2

private theorem exists_conj_normalizer_of_conj_centralizer {σ₁ : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({σ₁} : Set G))) {t z c : G}
    (htC : t ∈ centralizer ({σ₁} : Set G)) (hzC : z ∈ centralizer ({σ₁} : Set G))
    (hcC : c ∈ centralizer ({σ₁} : Set G)) (hc : c * t * c⁻¹ = z)
    (htZ : ∀ x ∈ T, x * t = t * x) (hzZ : ∀ x ∈ T, x * z = z * x) :
    ∃ n ∈ Subgroup.normalizer (T : Set G) ⊓ centralizer ({σ₁} : Set G), n * t * n⁻¹ = z := by
  let C : Subgroup G := centralizer ({σ₁} : Set G)
  obtain ⟨n, hnN, hn_t⟩ := exists_conj_normalizer_subgroupOf hT htC hzC hcC hc htZ hzZ
  have hn_t' : n.1⁻¹ * t * n.1 = z := by
    have := congrArg (fun y : C => (y : G)) hn_t
    simpa using this
  have hnG : n.1⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.inv_mem _ (mem_normalizer_of_mem_normalizer_subgroupOf hT.le hnN)
  exact ⟨n.1⁻¹, ⟨hnG, C.inv_mem n.2⟩, by simpa [inv_inv] using hn_t'⟩

omit [Finite G] in
private lemma ncard_sqrt_eq_natCard (T : Subgroup G) (a : G) :
    {k : G | k ∈ T ∧ k * k = a}.ncard = Nat.card {x : T // (x : G) * x = a} := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun k => ⟨⟨k.1, k.2.1⟩, k.2.2⟩
      invFun := fun x => ⟨((x.1 : T) : G), x.1.2, x.2⟩
      left_inv := fun k => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }

theorem ncard_sqrt_eq_of_isConj (h : Tim79a.ParrottHyp z) {σ₁ σ σ₃ w₁ : G}
    {T₁ S₀ : Subgroup G}
    (hσ₁ : orderOf σ₁ = 3) (hσ₁H : σ₁ ∈ H z) (hw₁H : w₁ ∈ H z) (hw₁ : w₁ * σ₁ * w₁⁻¹ = σ₁⁻¹)
    (hcls : ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ h ∈ H z, CFSG.conjugate R h = zpowers σ₁ ∨ CFSG.conjugate R h = zpowers σ ∨
        CFSG.conjugate R h = zpowers σ₃)
    (hσσ₁ : ∀ g : G, CFSG.conjugate (zpowers σ) g ≠ zpowers σ₁)
    (hE₃ : (∃ E : Subgroup G, E ≤ centralizer ({σ₃} : Set G) ∧ Nat.card E = 16 ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1) ∨
      ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({σ₃} : Set G)) ∧ Nat.card T = 2 ^ 5)
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ centralizer ({σ₁} : Set G))) (hT₁c : Nat.card T₁ = 2 ^ 7)
    (hnoE : ∀ F : Subgroup G, F ≤ T₁ → Nat.card F = 16 →
      ¬ ((∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1))
    (hS₀ : IsSylowOf 2 S₀ (H z ⊓ normalizer (zpowers σ₁ : Set G))) (hTS : T₁ ≤ S₀)
    (hZS₀ : ∀ e ∈ centerIn S₀, IsConj z e → e = z)
    {t : G} (htT : t ∈ centerIn T₁) (hzt : IsConj z t) :
    {k : G | k ∈ T₁ ∧ k * k = z}.ncard = {k : G | k ∈ T₁ ∧ k * k = t}.ncard := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁C : IsSylowOf 2 T₁ (centralizer ({σ₁} : Set G)) :=
    isSylowOf_centralizer_of_centerIn_normalizer h hσ₁H hT₁ hS₀ hTS hZS₀
  have hne₃ : ∀ g : G, CFSG.conjugate (zpowers σ₁) g ≠ zpowers σ₃ :=
    conjugate_zpowers_ne_of_elementaryAbelian_or_card hT₁C hT₁c hnoE hE₃
  have hneσ : ∀ g : G, CFSG.conjugate (zpowers σ₁) g ≠ zpowers σ := by
    intro g hg
    have h' : Subgroup.zpowers σ₁ = CFSG.conjugate (Subgroup.zpowers σ) g⁻¹ := by
      have h'' := congrArg (fun P => CFSG.conjugate P g⁻¹) hg
      rwa [CFSG.LocalCores.conjugate_conjugate, mul_inv_cancel,
        CFSG.GH74.GLS.C3.Layer1.Back.conjugate_one'] at h''
    exact hσσ₁ g⁻¹ h'.symm
  have hstar := star_of_orderThree_classes hcls hσ₁ hneσ hne₃
  have ht2 : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hzt
    rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, h.1]
  have htH : t ∈ H z := (hT₁.le htT.1).1
  have htσ : t ∈ centralizer ({σ₁} : Set G) := (hT₁.le htT.1).2
  obtain ⟨c, hcC, hc⟩ :=
    exists_centralizer_conj_of_isConj hσ₁ hσ₁H hstar hw₁H hw₁ ht2 htH htσ hzt
  have hzT : z ∈ centerIn T₁ := z_mem_centerIn_of_isSylowOf h hσ₁H hT₁
  have hzC : z ∈ centralizer ({σ₁} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hσ₁H).symm
  obtain ⟨n, ⟨hnN, _⟩, hnt⟩ :=
    exists_conj_normalizer_of_conj_centralizer hT₁C htσ hzC hcC hc
      (fun x hx => Subgroup.mem_centralizer_iff.mp htT.2 x hx)
      (fun x hx => Subgroup.mem_centralizer_iff.mp hzT.2 x hx)
  have hroot := CFSG.EvenSporadicStandard.HSStd.card_sq_eq_conj T₁ (n := n) hnN t
  rw [hnt] at hroot
  rw [ncard_sqrt_eq_natCard T₁ z, ncard_sqrt_eq_natCard T₁ t]
  exact hroot.symm

theorem mem_commutator_centralizer_z1 (h : Tim79a.ParrottHyp z) {z₁ σ₁ σ σ₃ w₁ t : G}
    {T₁ S₀ : Subgroup G}
    (hσ₁ : orderOf σ₁ = 3) (hσ₁H : σ₁ ∈ H z) (hw₁H : w₁ ∈ H z) (hw₁ : w₁ * σ₁ * w₁⁻¹ = σ₁⁻¹)
    (hcls : ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ h ∈ H z, CFSG.conjugate R h = zpowers σ₁ ∨ CFSG.conjugate R h = zpowers σ ∨
        CFSG.conjugate R h = zpowers σ₃)
    (hσσ₁ : ∀ g : G, CFSG.conjugate (zpowers σ) g ≠ zpowers σ₁)
    (hE₃ : (∃ E : Subgroup G, E ≤ centralizer ({σ₃} : Set G) ∧ Nat.card E = 16 ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1) ∨
      ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({σ₃} : Set G)) ∧ Nat.card T = 2 ^ 5)
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ centralizer ({σ₁} : Set G))) (hT₁c : Nat.card T₁ = 2 ^ 7)
    (hnoE : ∀ F : Subgroup G, F ≤ T₁ → Nat.card F = 16 →
      ¬ ((∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1))
    (hS₀ : IsSylowOf 2 S₀ (H z ⊓ normalizer (zpowers σ₁ : Set G))) (hTS : T₁ ≤ S₀)
    (hZS₀ : ∀ e ∈ centerIn S₀, IsConj z e → e = z)
    (hz₁T : z₁ ∈ centerIn T₁) (htT : t ∈ centerIn T₁)
    (hzt : IsConj z t) (hztz : IsConj z (t * z))
    (hsq : z₁ ∈ ⁅T₁, T₁⁆ ∨
      {k : G | k ∈ T₁ ∧ k * k = z}.ncard ≠ {k : G | k ∈ T₁ ∧ k * k = t}.ncard ∨
      {k : G | k ∈ T₁ ∧ k * k = z}.ncard ≠ {k : G | k ∈ T₁ ∧ k * k = t * z}.ncard) :
    z₁ ∈ ⁅centralizer ({z₁} : Set G), centralizer ({z₁} : Set G)⁆ := by
  have hzT : z ∈ centerIn T₁ := z_mem_centerIn_of_isSylowOf h hσ₁H hT₁
  have htzT : t * z ∈ centerIn T₁ := (centerIn T₁).mul_mem htT hzT
  have hT₁C : T₁ ≤ centralizer ({z₁} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hz₁T.2 x hx
  have hz₁comm : z₁ ∈ ⁅T₁, T₁⁆ := by
    rcases hsq with h1 | h1 | h1
    · exact h1
    · exact absurd
        (ncard_sqrt_eq_of_isConj h hσ₁ hσ₁H hw₁H hw₁ hcls hσσ₁ hE₃ hT₁ hT₁c hnoE hS₀ hTS
          hZS₀ htT hzt) h1
    · exact absurd
        (ncard_sqrt_eq_of_isConj h hσ₁ hσ₁H hw₁H hw₁ hcls hσσ₁ hE₃ hT₁ hT₁c hnoE hS₀ hTS
          hZS₀ htzT hztz) h1
  exact Subgroup.commutator_mono hT₁C hT₁C hz₁comm

end CFSG.RankThree.GF2n.Parrott
