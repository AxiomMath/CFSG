module

public import CFSG.RankThree.PartOne.S12.Sec12Fus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

namespace KFU

variable {G : Type} [Group G]

theorem conj_mem_zpowers_of_commute {c y : G} (hyc : y * c = c * y) {g : G}
    (hg : g ∈ Subgroup.zpowers c) : y * g * y⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have : y * c ^ k * y⁻¹ = c ^ k := by
    have h1 : Commute y (c ^ k) := Commute.zpow_right (show Commute y c from hyc) k
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.eq
  rw [this]
  exact Subgroup.zpow_mem_zpowers c k

theorem mem_cNormalizer_of_commute {c x : G} (hxc : x * c = c * x) : x ∈ cNormalizer c := by
  unfold cNormalizer
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact conj_mem_zpowers_of_commute hxc
  · intro hg
    have hx' : x⁻¹ * c = c * x⁻¹ := (Commute.inv_left (show Commute x c from hxc)).eq
    have := conj_mem_zpowers_of_commute hx' hg
    simpa [mul_assoc] using this

theorem exists_mul_normalizer_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {H C S : Subgroup G}
    (hCn : ∀ h ∈ H, ∀ x ∈ C, h * x * h⁻¹ ∈ C) (hS : IsSylowOf p S H) (hSC : S ≤ C) :
    ∀ g ∈ H, ∃ x ∈ C, ∃ n ∈ H, n ∈ Subgroup.normalizer (S : Set G) ∧ g = x * n := by
  classical
  obtain ⟨hSH, hSp, hidx⟩ := hS
  have hNn : (C.subgroupOf H).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hCn h h.2 x hx⟩
  have hSp' : IsPGroup p (S.subgroupOf H) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨P, hP⟩ : ∃ P : Sylow p ↥H, (P : Subgroup ↥H) = S.subgroupOf H :=
    ⟨hSp'.toSylow hidx, IsPGroup.toSylow_coe _ _⟩
  have hPN : P ≤ C.subgroupOf H := by
    show (P : Subgroup ↥H) ≤ C.subgroupOf H
    rw [hP]
    exact Subgroup.subgroupOf_mono H hSC
  have hfr := Sylow.normalizer_sup_eq_top' (N := C.subgroupOf H) P hPN
  intro g hg
  have hgtop : (⟨g, hg⟩ : ↥H) ∈ Subgroup.normalizer ((P : Subgroup ↥H) : Set ↥H) ⊔
      C.subgroupOf H := by
    have h := Subgroup.mem_top (⟨g, hg⟩ : ↥H)
    rw [← hfr] at h
    exact h
  obtain ⟨n', hn', x', hx', hnx⟩ := Subgroup.mem_sup_of_normal_right.1 hgtop
  refine ⟨(n' : G) * (x' : G) * (n' : G)⁻¹, ?_, (n' : G), n'.2, ?_, ?_⟩
  · exact hCn _ n'.2 _ (Subgroup.mem_subgroupOf.1 hx')
  · have h1 : n' ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [← hP]
      exact hn'
    have h2 : n' ∈ (Subgroup.normalizer (S : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hSH]
      exact h1
    exact h2
  · have := congrArg Subtype.val hnx
    simp only [Subgroup.coe_mul] at this
    rw [← this]
    group

theorem conj_mem_centralizer_of_mem_cNormalizer {c h x : G} (hh : h ∈ cNormalizer c)
    (hx : x ∈ Subgroup.centralizer ({c} : Set G)) :
    h * x * h⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    ((Subgroup.mem_normalizer_iff.1 ((cNormalizer c).inv_mem hh) c).1 (Subgroup.mem_zpowers c))
  have hcj : c = h * c ^ j * h⁻¹ := by
    rw [hj]
    group
  have hxj : x * c ^ j = c ^ j * x := (Commute.zpow_right (show Commute x c from hxc) j).eq
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  calc h * x * h⁻¹ * c = h * x * h⁻¹ * (h * c ^ j * h⁻¹) := by rw [← hcj]
    _ = h * (x * c ^ j) * h⁻¹ := by group
    _ = h * (c ^ j * x) * h⁻¹ := by rw [hxj]
    _ = (h * c ^ j * h⁻¹) * (h * x * h⁻¹) := by group
    _ = c * (h * x * h⁻¹) := by rw [← hcj]

theorem pH_le_centralizer [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (ctx : Fus12Ctx G p A c L E) {I P Q : Subgroup G} (hout : Out1214 p c L E I P Q) :
    P ⊓ cNormalizer c ≤ Subgroup.centralizer ({c} : Set G) := by
  classical
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hcA : c ∈ A := h.c_mem
  have hcE : c ∈ E := h.A_le_E hcA
  have hcL : c ∉ L := ctx.c_not_mem
  have hcp : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c hcA
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hEP : E ≤ P := by
    rw [← hout.omega]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hcP : c ∈ P := hEP hcE
  have hcQ : c ∉ Q := fun hQ => by
    have : c ∈ Q ⊓ E := ⟨hQ, hcE⟩
    rw [hout.QE] at this
    exact hcL this.2
  obtain ⟨f, hfP, hPf⟩ := hout.P_gen
  have hab := quotient_abelian_of_sup_zpowers hout.Q_norm.1 hout.Q_norm.2 hfP hPf
  rintro y ⟨hyP, hyH⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    ((Subgroup.mem_normalizer_iff.1 hyH c).1 (Subgroup.mem_zpowers c))
  have hcomm : y * c * y⁻¹ * c⁻¹ ∈ Q := Subgroup.mem_subgroupOf.1 (hab ⟨y, hyP⟩ ⟨c, hcP⟩)
  have hd : c ^ (k - 1) ∈ Q := by
    have : c ^ (k - 1) = y * c * y⁻¹ * c⁻¹ := by rw [← hk, zpow_sub, zpow_one]
    rw [this]
    exact hcomm
  have hd1 : c ^ (k - 1) = 1 := by
    by_contra hne
    have hdp : (c ^ (k - 1)) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
    have hord : orderOf (c ^ (k - 1)) = p := orderOf_eq_prime hdp hne
    have hle : Subgroup.zpowers (c ^ (k - 1)) ≤ Subgroup.zpowers c :=
      Subgroup.zpowers_le.2 (Subgroup.zpow_mem_zpowers c _)
    have heq : Subgroup.zpowers (c ^ (k - 1)) = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hcord])
    have hcd : c ∈ Subgroup.zpowers (c ^ (k - 1)) := heq ▸ Subgroup.mem_zpowers c
    exact hcQ (Subgroup.zpowers_le.2 hd hcd)
  have hck : c ^ k = c := by
    rw [show k = (k - 1) + 1 by ring, zpow_add, hd1, one_mul, zpow_one]
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have h2 : y * c * y⁻¹ = c := by rw [← hk, hck]
  calc y * c = (y * c * y⁻¹) * y := by group
    _ = c * y := by rw [h2]

theorem frat_core [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (ctx : Fus12Ctx G p A c L E) {I P Q : Subgroup G} (hout : Out1214 p c L E I P Q) :
    ∀ g ∈ cNormalizer c, ∃ x ∈ Subgroup.centralizer ({c} : Set G),
      ∃ n ∈ cNormalizer c ⊓ torusNormalizer E, g = x * n := by
  classical
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hEP : E ≤ P := by
    rw [← hout.omega]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hEel := h.E_elem
  have hEH : E ≤ cNormalizer c := fun e he =>
    mem_cNormalizer_of_commute (by
      have := (inferInstance : IsMulCommutative E).is_comm.comm ⟨e, he⟩ ⟨c, hcE⟩
      exact congrArg Subtype.val this)
  have hEPH : E ≤ P ⊓ cNormalizer c := le_inf hEP hEH
  have hPC := pH_le_centralizer ctx hout
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ cNormalizer c := fun x hx =>
    mem_cNormalizer_of_commute (Subgroup.mem_centralizer_singleton_iff.1 hx)
  have key : ∀ m ∈ Subgroup.normalizer ((P ⊓ cNormalizer c : Subgroup G) : Set G),
      ∀ e ∈ E, m * e * m⁻¹ ∈ E := by
    intro m hm e he
    have hmem : m * e * m⁻¹ ∈ P ⊓ cNormalizer c :=
      (Subgroup.mem_normalizer_iff.1 hm e).1 (hEPH he)
    have hpow : (m * e * m⁻¹) ^ p = 1 := by
      rw [conj_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he]
      group
    rw [← hout.omega]
    exact Subgroup.subset_closure ⟨hmem.1, hpow⟩
  intro g hg
  obtain ⟨x, hx, n, hn, hnS, hgxn⟩ := exists_mul_normalizer_of_isSylowOf
    (p := p) (H := cNormalizer c) (C := Subgroup.centralizer ({c} : Set G))
    (S := P ⊓ cNormalizer c) (fun h' hh x hx => conj_mem_centralizer_of_mem_cNormalizer hh hx)
    hout.H_sylow hPC g hg
  refine ⟨x, hx, n, ⟨hn, ?_⟩, hgxn⟩
  show n ∈ Subgroup.normalizer (E : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact key n hnS e he
  · intro he
    have := key n⁻¹ ((Subgroup.normalizer _).inv_mem hnS) (n * e * n⁻¹) he
    simpa [mul_assoc] using this

end KFU

end CFSG.RankThree.PartOne
