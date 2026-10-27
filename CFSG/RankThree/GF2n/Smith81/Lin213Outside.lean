module

public import CFSG.RankThree.GF2n.Smith81.TiRootLines
public import CFSG.CGT.Timmesfeld75.SLTransvectionOrder
public import CFSG.RankThree.GF2n.Smith81.Sec220DihLin
public import CFSG.RankThree.GF2n.Smith81.Lin213Elem

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix Pointwise MatrixGroups

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {x t : G} (hx : x * x = 1)
    (ht : t ∈ Subgroup.zpowers x) : t = 1 ∨ t = x := by
  obtain ⟨k, rfl⟩ := ht
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  have e : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, hx2, one_zpow, mul_one]
  simp only at e ⊢
  rw [e]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem sqZero_mul_eq_zero {K : Type*} [Field K] {n : ℕ} {N₁ N₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0)
    (h : LinearMap.range N₁.mulVecLin = LinearMap.range N₂.mulVecLin ∨
      LinearMap.ker N₁.mulVecLin = LinearMap.ker N₂.mulVecLin) :
    N₁ * N₂ = 0 ∧ N₂ * N₁ = 0 := by
  have hsq : ∀ {A : Matrix (Fin n) (Fin n) K}, A * A = 0 →
      LinearMap.range A.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    rintro A hA _ ⟨w, rfl⟩
    simp [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA]
  have key : ∀ {A B : Matrix (Fin n) (Fin n) K},
      LinearMap.range B.mulVecLin ≤ LinearMap.ker A.mulVecLin → A * B = 0 := by
    intro A B hB
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, map_zero]
    refine LinearMap.ext fun v => ?_
    have h := hB ⟨v, rfl⟩
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.toLin'_apply] using h
  rcases h with h | h
  · exact ⟨key (h ▸ hsq h₁), key (h.symm ▸ hsq h₂)⟩
  · exact ⟨key (h ▸ hsq h₂), key (h.symm ▸ hsq h₁)⟩

theorem sq_isTransvection_of_orderOf_eq_four {F : Type*} [Field F] [CharP F 2] [Finite F]
    {n : ℕ} {u₁ u₂ : SL(n, F)} (h₁ : IsTransvection u₁) (h₂ : IsTransvection u₂)
    (h4 : orderOf (u₁ * u₂) = 4) : IsTransvection ((u₁ * u₂) ^ 2) := by
  obtain ⟨f₁, v₁, hfv₁, -, hu₁⟩ := h₁.exists_data
  obtain ⟨f₂, v₂, hfv₂, -, hu₂⟩ := h₂.exists_data
  have hc : f₁ v₂ * f₂ v₁ = 0 := by
    by_contra hc
    exact not_two_dvd_orderOf_mul hfv₁ hfv₂ hu₁ hu₂ hc (h4 ▸ ⟨2, rfl⟩)
  have hne : (u₁ * u₂) ^ 2 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega
  set a := f₁ v₂ with ha
  set b := f₂ v₁ with hb
  let N : (Fin n → F) → (Fin n → F) := fun x => f₂ x • v₂ + (f₁ x + a * f₂ x) • v₁
  have hw : ∀ x, sact (u₁ * u₂) x = x + N x := fun x => sact_mul_transvection hu₁ hu₂ x
  have hNadd : ∀ x y, N (x + y) = N x + N y := by
    intro x y
    simp only [N, map_add, add_smul, mul_add]
    abel
  have hf₂N : ∀ x, f₂ (N x) = b * (f₁ x + a * f₂ x) := by
    intro x
    simp only [N, map_add, map_smul, smul_eq_mul, hfv₂]
    rw [← hb]
    ring
  have hf₁N : ∀ x, f₁ (N x) = a * f₂ x := by
    intro x
    simp only [N, map_add, map_smul, smul_eq_mul, hfv₁]
    rw [← ha]
    ring
  have hsq : ∀ y, sact ((u₁ * u₂) ^ 2) y = y + N (N y) := by
    intro y
    have h := vec_add_self (N y)
    rw [pow_two, sact_mul, hw y, hw (y + N y), hNadd y (N y)]
    calc y + N y + (N y + N (N y)) = y + (N y + N y) + N (N y) := by abel
      _ = y + N (N y) := by rw [h, add_zero]
  obtain ⟨g, w, hgw, hNN⟩ : ∃ (g : Module.Dual F (Fin n → F)) (w : Fin n → F), g w = 0 ∧
      ∀ x, N (N x) = g x • w := by
    rcases mul_eq_zero.mp hc with h0 | h0
    · refine ⟨b • f₁, v₂, by simp [← ha, h0], fun x => ?_⟩
      show f₂ (N x) • v₂ + (f₁ (N x) + a * f₂ (N x)) • v₁ = _
      rw [hf₂N, hf₁N, h0]
      simp
    · refine ⟨a • f₂, v₁, by simp [← hb, h0], fun x => ?_⟩
      show f₂ (N x) • v₂ + (f₁ (N x) + a * f₂ (N x)) • v₁ = _
      rw [hf₂N, hf₁N, h0]
      simp
  refine ⟨hne, g, w, hgw, LinearEquiv.ext fun x => ?_⟩
  rw [Matrix.SpecialLinearGroup.toLin'_apply, LinearEquiv.transvection.apply]
  show sact ((u₁ * u₂) ^ 2) x = _
  rw [hsq, hNN]

theorem transv_mul_orderOf {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {u₁ u₂ : SL(n, F)} (h₁ : IsTransvection u₁) (h₂ : IsTransvection u₂) (hne : u₁ ≠ u₂) :
    orderOf (u₁ * u₂) = 2 ∨ (orderOf (u₁ * u₂) = 4 ∧ IsTransvection ((u₁ * u₂) ^ 2)) ∨
      Odd (orderOf (u₁ * u₂)) := by
  rcases h₁.orderOf_mul_cases h₂ with h | h
  · have h1 : orderOf (u₁ * u₂) ≠ 1 := by
      intro e
      rw [orderOf_eq_one_iff] at e
      obtain ⟨f₁, v₁, hfv₁, -, hu₁⟩ := h₁.exists_data
      have hinv : u₁ * u₁ = 1 := mul_self_eq_one_of_transvection hfv₁ hu₁
      apply hne
      calc u₁ = u₁ * (u₁ * u₂) := by rw [e, mul_one]
        _ = u₂ := by rw [← mul_assoc, hinv, one_mul]
    have hpos : 0 < orderOf (u₁ * u₂) := Nat.pos_of_dvd_of_pos h (by norm_num)
    have hle : orderOf (u₁ * u₂) ≤ 4 := Nat.le_of_dvd (by norm_num) h
    interval_cases hk : orderOf (u₁ * u₂)
    · exact absurd rfl h1
    · exact Or.inl rfl
    · exact absurd h (by norm_num)
    · exact Or.inr (Or.inl ⟨rfl, sq_isTransvection_of_orderOf_eq_four h₁ h₂ hk⟩)
  · exact Or.inr (Or.inr h)

theorem transv_conj_SL {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {u₁ u₂ : SL(n, F)} (h₁ : IsTransvection u₁) (h₂ : IsTransvection u₂) :
    ∃ W : SL(n, F), W * u₁ * W⁻¹ = u₂ :=
  exists_conj_of_isTransvection h₁ h₂

theorem ker_sup_ker_eq_top {K : Type*} [Field K] {n : ℕ} {N₁ N₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : N₁.rank = 1) (h₂ : N₂.rank = 1)
    (hne : LinearMap.ker N₁.mulVecLin ≠ LinearMap.ker N₂.mulVecLin) :
    LinearMap.ker N₁.mulVecLin ⊔ LinearMap.ker N₂.mulVecLin = ⊤ := by
  have hk : ∀ {N : Matrix (Fin n) (Fin n) K}, N.rank = 1 →
      Module.finrank K (LinearMap.ker N.mulVecLin) + 1 = n := by
    intro N hN
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [show Module.finrank K (LinearMap.range N.mulVecLin) = N.rank from rfl, hN,
      Module.finrank_fin_fun] at this
    omega
  have e₁ := hk h₁
  have e₂ := hk h₂
  have hlt : LinearMap.ker N₁.mulVecLin <
      LinearMap.ker N₁.mulVecLin ⊔ LinearMap.ker N₂.mulVecLin := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    have hle : LinearMap.ker N₂.mulVecLin ≤ LinearMap.ker N₁.mulVecLin := h ▸ le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hf := Submodule.finrank_lt_finrank_of_lt hlt
  have htop := Submodule.finrank_le
    (LinearMap.ker N₁.mulVecLin ⊔ LinearMap.ker N₂.mulVecLin)
  rw [Module.finrank_fin_fun] at htop
  exact Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)

theorem range_inf_range_eq_bot {K : Type*} [Field K] {n : ℕ} {N₁ N₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : N₁.rank = 1) (h₂ : N₂.rank = 1)
    (hne : LinearMap.range N₁.mulVecLin ≠ LinearMap.range N₂.mulVecLin) :
    LinearMap.range N₁.mulVecLin ⊓ LinearMap.range N₂.mulVecLin = ⊥ := by
  set R₁ := LinearMap.range N₁.mulVecLin
  set R₂ := LinearMap.range N₂.mulVecLin
  have e₁ : Module.finrank K R₁ = 1 := h₁
  have e₂ : Module.finrank K R₂ = 1 := h₂
  by_contra hb
  have hpos : Module.finrank K ↥(R₁ ⊓ R₂) ≠ 0 := fun h0 =>
    hb (Submodule.finrank_eq_zero.mp h0)
  have hle₁ := Submodule.finrank_mono (inf_le_left : R₁ ⊓ R₂ ≤ R₁)
  have hle₂ := Submodule.finrank_mono (inf_le_right : R₁ ⊓ R₂ ≤ R₂)
  have u₁ : R₁ ⊓ R₂ = R₁ := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  have u₂ : R₁ ⊓ R₂ = R₂ := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  exact hne (u₁.symm.trans u₂)

variable {G : Type} [Group G] [Finite G]

theorem Sit.inf_QB_sup_Z_comm {M Q Z X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    IsElemAbelian 2 ((Q ⊓ QB X) ⊔ Z) ∧ ∀ d ∈ (Q ⊓ QB X) ⊔ Z, x * d = d * x := by
  set A := Q ⊓ QB X
  obtain ⟨hAc, hA2⟩ := hs.inf_QB_elemAbelian
  have hZc : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z := by
    intro z hz q hq
    have hz' : z ∈ cen Q := hs.hyp.hZ ▸ hz
    rw [cen_eq] at hz'
    exact (Subgroup.mem_centralizer_iff.mp hz'.2 q hq).symm
  have hZQ : Z ≤ Q := by
    intro z hz
    have hz' : z ∈ cen Q := hs.hyp.hZ ▸ hz
    rw [cen_eq] at hz'
    exact hz'.1
  have hAA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hle : A ⊔ Z ≤ Q := sup_le inf_le_left hZQ
  have hAcen : A ⊔ Z ≤ Subgroup.centralizer (A : Set G) := by
    refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hAA b hb a ha) ?_
    exact fun z hz => Subgroup.mem_centralizer_iff.mpr fun b hb => (hZc z hz b hb.1).symm
  have hZcen : A ⊔ Z ≤ Subgroup.centralizer (Z : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => hZc z hz g (hle hg)
  have hcomm : ∀ a ∈ A ⊔ Z, ∀ b ∈ A ⊔ Z, a * b = b * a := by
    intro a ha b hb
    have hcen : A ⊔ Z ≤ Subgroup.centralizer ((A ⊔ Z : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · intro c hc
        exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
          (Subgroup.mem_centralizer_iff.mp (hAcen hd) c hc).symm
      · intro c hc
        exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
          (Subgroup.mem_centralizer_iff.mp (hZcen hd) c hc).symm
    exact (Subgroup.mem_centralizer_iff.mp (hcen hb) a ha)
  have hsq : ∀ g ∈ A ⊔ Z, g ^ 2 = 1 := by
    let H : Subgroup G :=
      { carrier := {g | g ∈ A ⊔ Z ∧ g ^ 2 = 1}
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          have hc : Commute a b := hcomm a ha.1 b hb.1
          rw [hc.mul_pow 2, ha.2, hb.2, one_mul]⟩
        one_mem' := ⟨one_mem _, one_pow _⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hH : A ⊔ Z ≤ H := sup_le (fun a ha => ⟨Subgroup.mem_sup_left ha, hA2 a ha⟩)
      (fun z hz => ⟨Subgroup.mem_sup_right hz, Z_sq hs.hyp hz⟩)
    exact fun g hg => (hH hg).2
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hsq⟩, ?_⟩
  have h12 := smith_1_12 hs
  obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
  have hxA : ∀ a ∈ A, x * a = a * x := by
    intro a ha
    have haQ : g⁻¹ * a * g ∈ Q := by
      have h' : a ∈ QB X := ha.2
      rw [hQB, mem_conjSubgroup] at h'; exact h'
    have hxZ : g⁻¹ * x * g ∈ Z := by
      have := hs.mem; rw [hg, mem_conjSubgroup] at this; exact this
    have h := hZc _ hxZ _ haQ
    have e : x * a = g * ((g⁻¹ * x * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    rw [e, h]; group
  have hxZ : ∀ z ∈ Z, x * z = z * x := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (h12.1 hs.mem).2 z hz).symm
  have hxC : A ⊔ Z ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hxA a ha).symm)
      (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (hxZ z hz).symm)
  exact fun d hd => (Subgroup.mem_centralizer_singleton_iff.mp (hxC hd)).symm

section B0

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}

theorem mem_comm_sup_iff_of_coord (hN : S ≤ Subgroup.normalizer (V : Set G))
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (hψ : ∀ (s : S) (v w : V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        act (φ s) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hZV : Z ≤ V) {s : S} (hs2 : (s : G) * s = 1) {g : G} (hg : g ∈ V) :
    g ∈ ⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z ↔
      Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨g, hg⟩)) ∈
        LinearMap.range (act (φ s) - 1).mulVecLin := by
  let F : ↥V → (ι → K) := fun v => Multiplicative.toAdd (ψ (QuotientGroup.mk v))
  have Fmul : ∀ a b : ↥V, F (a * b) = F a + F b := by
    intro a b
    show Multiplicative.toAdd (ψ (QuotientGroup.mk (a * b))) = _
    rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
  have Finv : ∀ a : ↥V, F a⁻¹ = - F a := by
    intro a
    show Multiplicative.toAdd (ψ (QuotientGroup.mk a⁻¹)) = _
    rw [QuotientGroup.mk_inv, map_inv, toAdd_inv]
  have Fzero : ∀ a : ↥V, F a = 0 ↔ (a : G) ∈ Z := by
    intro a
    have e : F a = 0 ↔ ψ (QuotientGroup.mk a) = 1 := by
      show Multiplicative.toAdd (ψ (QuotientGroup.mk a)) = 0 ↔ _
      constructor
      · intro h
        have := congrArg Multiplicative.ofAdd h
        simpa using this
      · intro h; rw [h]; rfl
    rw [e, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hsV : ∀ v ∈ V, (s : G) * v * (s : G)⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (hN s.2) v).mp hv
  have hcV : ∀ v ∈ V, ⁅v, (s : G)⁆ ∈ V := by
    intro v hv
    have e : ⁅v, (s : G)⁆ = v * ((s : G) * v⁻¹ * (s : G)⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv (hsV _ (V.inv_mem hv))
  have hψF : ∀ (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ → F w = act (φ s) *ᵥ F v :=
    fun v w h => hψ s v w h
  have Fcomm : ∀ (v : ↥V), F ⟨⁅(v : G), (s : G)⁆, hcV v v.2⟩ = (act (φ s) - 1) *ᵥ (- F v) := by
    intro v
    have hw : (s : G) * (v⁻¹ : ↥V) * (s : G)⁻¹ ∈ V := hsV _ (v⁻¹).2
    have e : (⟨⁅(v : G), (s : G)⁆, hcV v v.2⟩ : ↥V) = v * ⟨_, hw⟩ := by
      ext; simp [commutatorElement_def, mul_assoc]
    rw [e, Fmul, hψF v⁻¹ ⟨_, hw⟩ rfl, Finv, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_neg]
    abel
  constructor
  ·
    intro hmem
    let P : Subgroup G :=
      { carrier := {x | ∃ hx : x ∈ V, F ⟨x, hx⟩ ∈ LinearMap.range (act (φ s) - 1).mulVecLin}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨V.mul_mem ha hb, ?_⟩
          have : F ⟨a * b, V.mul_mem ha hb⟩ = F ⟨a, ha⟩ + F ⟨b, hb⟩ := Fmul ⟨a, ha⟩ ⟨b, hb⟩
          rw [this]; exact Submodule.add_mem _ ha' hb'
        one_mem' := ⟨V.one_mem, by
          have : F ⟨1, V.one_mem⟩ = 0 := (Fzero _).mpr Z.one_mem
          rw [this]; exact Submodule.zero_mem _⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨V.inv_mem ha, ?_⟩
          have : F ⟨a⁻¹, V.inv_mem ha⟩ = - F ⟨a, ha⟩ := Finv ⟨a, ha⟩
          rw [this]; exact Submodule.neg_mem _ ha' }
    have hle : ⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z ≤ P := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro v hv t ht
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
        have hs2' : (s : G) ^ (2 : ℤ) = 1 := by rw [zpow_two, hs2]
        rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
        · rw [zpow_mul, hs2', one_zpow, commutatorElement_one_right]
          exact P.one_mem
        · rw [zpow_add, zpow_mul, hs2', one_zpow, one_mul, zpow_one]
          refine ⟨hcV v hv, ?_⟩
          have := Fcomm ⟨v, hv⟩
          rw [this]
          exact LinearMap.mem_range.mpr ⟨_, rfl⟩
      · intro z hz
        exact ⟨hZV hz, by rw [(Fzero ⟨z, hZV hz⟩).mpr hz]; exact Submodule.zero_mem _⟩
    obtain ⟨_, h⟩ := hle hmem
    exact h
  ·
    rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ := ψ.surjective (Multiplicative.ofAdd (- u))
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    have hFw : F w = - u := by
      show Multiplicative.toAdd (ψ (QuotientGroup.mk w)) = _
      rw [hw]; rfl
    have hFc : F ⟨_, hcV w w.2⟩ = F ⟨g, hg⟩ := by
      rw [Fcomm w, hFw, neg_neg]
      exact hu
    have hz : g * (⁅(w : G), (s : G)⁆)⁻¹ ∈ Z := by
      have h0 : F (⟨g, hg⟩ * (⟨_, hcV w w.2⟩ : ↥V)⁻¹) = 0 := by
        rw [Fmul, Finv, hFc, add_neg_cancel]
      simpa using (Fzero _).mp h0
    have e : g = (g * (⁅(w : G), (s : G)⁆)⁻¹) * ⁅(w : G), (s : G)⁆ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz)
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator w.2 (Subgroup.mem_zpowers _)))

end B0

theorem coord_eq_zero_iff {ι : Type} {K : Type} [Field K] {V Z : Subgroup G}
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (a : ↥V) :
    Multiplicative.toAdd (ψ (QuotientGroup.mk a)) = 0 ↔ (a : G) ∈ Z := by
  have e : Multiplicative.toAdd (ψ (QuotientGroup.mk a)) = 0 ↔ ψ (QuotientGroup.mk a) = 1 := by
    constructor
    · intro h
      have := congrArg Multiplicative.ofAdd h
      simpa using this
    · intro h; rw [h]; rfl
  rw [e, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem comm_sup_le_of_normalizer {S V Z : Subgroup G} (hN : S ≤ Subgroup.normalizer (V : Set G))
    (hZV : Z ≤ V) {s : G} (hs : s ∈ S) : ⁅V, Subgroup.zpowers s⁆ ⊔ Z ≤ V := by
  refine sup_le ?_ hZV
  rw [Subgroup.commutator_le]
  intro v hv t ht
  have htS : t ∈ S := (Subgroup.zpowers_le.mpr hs) ht
  have e : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hN htS) _).mp (V.inv_mem hv))

theorem SectionAct.comm_sup_eq_of_range_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (h : SectionAct K S V Z φ act) (hZV : Z ≤ V) {s t : S} (hs2 : (s : G) * s = 1)
    (ht2 : (t : G) * t = 1)
    (hr : LinearMap.range (act (φ s) - 1).mulVecLin =
      LinearMap.range (act (φ t) - 1).mulVecLin) :
    ⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z = ⁅V, Subgroup.zpowers (t : G)⁆ ⊔ Z := by
  obtain ⟨hN, hZn, ψ, hψ⟩ := h
  ext g
  constructor
  · intro hg
    have hgV := comm_sup_le_of_normalizer hN hZV s.2 hg
    rw [mem_comm_sup_iff_of_coord hN ψ hψ hZV ht2 hgV, ← hr]
    exact (mem_comm_sup_iff_of_coord hN ψ hψ hZV hs2 hgV).mp hg
  · intro hg
    have hgV := comm_sup_le_of_normalizer hN hZV t.2 hg
    rw [mem_comm_sup_iff_of_coord hN ψ hψ hZV hs2 hgV, hr]
    exact (mem_comm_sup_iff_of_coord hN ψ hψ hZV ht2 hgV).mp hg

theorem SectionAct.comm_sup_inf_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (h : SectionAct K S V Z φ act) (hZV : Z ≤ V) {s t : S} (hs2 : (s : G) * s = 1)
    (ht2 : (t : G) * t = 1)
    (hr : LinearMap.range (act (φ s) - 1).mulVecLin ⊓
      LinearMap.range (act (φ t) - 1).mulVecLin = ⊥) :
    (⁅V, Subgroup.zpowers (s : G)⁆ ⊔ Z) ⊓ (⁅V, Subgroup.zpowers (t : G)⁆ ⊔ Z) = Z := by
  obtain ⟨hN, hZn, ψ, hψ⟩ := h
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  rintro g ⟨hgs, hgt⟩
  have hgV := comm_sup_le_of_normalizer hN hZV s.2 hgs
  have h1 := (mem_comm_sup_iff_of_coord hN ψ hψ hZV hs2 hgV).mp hgs
  have h2 := (mem_comm_sup_iff_of_coord hN ψ hψ hZV ht2 hgV).mp hgt
  have h3 : _ ∈ (⊥ : Submodule K (ι → K)) := hr ▸ Submodule.mem_inf.mpr ⟨h1, h2⟩
  rw [Submodule.mem_bot] at h3
  exact (coord_eq_zero_iff ψ ⟨g, hgV⟩).mp h3

theorem SectionAct.exists_mul_of_ker_sup {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {S V Z : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (h : SectionAct K S V Z φ act) {s t : S}
    (hk : LinearMap.ker (act (φ s) - 1).mulVecLin ⊔
      LinearMap.ker (act (φ t) - 1).mulVecLin = ⊤) {v : G} (hv : v ∈ V) :
    ∃ c ∈ V, ∃ c' ∈ V, v = c * c' ∧ ⁅(s : G), c⁆ ∈ Z ∧ ⁅(t : G), c'⁆ ∈ Z := by
  obtain ⟨hN, hZn, ψ, hψ⟩ := h
  let F : ↥V → (ι → K) := fun v => Multiplicative.toAdd (ψ (QuotientGroup.mk v))
  have Fmul : ∀ a b : ↥V, F (a * b) = F a + F b := by
    intro a b
    show Multiplicative.toAdd (ψ (QuotientGroup.mk (a * b))) = _
    rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
  have Finv : ∀ a : ↥V, F a⁻¹ = - F a := by
    intro a
    show Multiplicative.toAdd (ψ (QuotientGroup.mk a⁻¹)) = _
    rw [QuotientGroup.mk_inv, map_inv, toAdd_inv]
  have key : ∀ (u : S) (c : ↥V), F c ∈ LinearMap.ker (act (φ u) - 1).mulVecLin →
      ⁅(u : G), (c : G)⁆ ∈ Z := by
    intro u c hc
    have hw : (u : G) * c * (u : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hN u.2) _).mp c.2
    have hFw : F ⟨_, hw⟩ = act (φ u) *ᵥ F c := hψ u c ⟨_, hw⟩ rfl
    have e : (⁅(u : G), (c : G)⁆ : G) = ((⟨_, hw⟩ : ↥V) * c⁻¹ : ↥V) := by
      simp [commutatorElement_def]
    rw [e, ← coord_eq_zero_iff ψ]
    change F (⟨_, hw⟩ * c⁻¹) = 0
    rw [Fmul, Finv, hFw]
    have : (act (φ u) - 1) *ᵥ F c = 0 := hc
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    rw [this, add_neg_cancel]
  have hmem : F ⟨v, hv⟩ ∈ LinearMap.ker (act (φ s) - 1).mulVecLin ⊔
      LinearMap.ker (act (φ t) - 1).mulVecLin := hk ▸ Submodule.mem_top
  obtain ⟨α, hα, α', hα', hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, hc⟩ := ψ.surjective (Multiplicative.ofAdd α)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
  have hFc : F c = α := by
    show Multiplicative.toAdd (ψ (QuotientGroup.mk c)) = _
    rw [hc]; rfl
  have hFc' : F (c⁻¹ * ⟨v, hv⟩) = α' := by
    rw [Fmul, Finv, hFc, ← hsum]; abel
  refine ⟨c, c.2, (c⁻¹ * ⟨v, hv⟩ : ↥V), (c⁻¹ * ⟨v, hv⟩ : ↥V).2, by simp, key s c (hFc ▸ hα),
    key t _ (hFc' ▸ hα')⟩

theorem sup_inf_sup_le {Z V₁ V₂ A₁ A₂ B₁ B₂ : Subgroup G} (hI : V₁ ⊓ V₂ = Z)
    (hA₁ : Z ≤ A₁) (hA₁V : A₁ ≤ V₁) (hA₂ : Z ≤ A₂) (hA₂V : A₂ ≤ V₂)
    (hB₁ : Z ≤ B₁) (hB₁V : B₁ ≤ V₁) (hB₂ : Z ≤ B₂) (hB₂V : B₂ ≤ V₂)
    (hcm : ∀ a ∈ V₁, ∀ b ∈ V₂, ⁅a, b⁆ ∈ Z) :
    (A₁ ⊔ A₂) ⊓ (B₁ ⊔ B₂) ≤ (A₁ ⊓ B₁) ⊔ (A₂ ⊓ B₂) := by
  have hconj : ∀ {C D : Subgroup G}, Z ≤ C → C ≤ V₁ → D ≤ V₂ →
      ∀ d ∈ D, ∀ c ∈ C, d * c * d⁻¹ ∈ C := by
    intro C D hZC hCV hDV d hd c hc
    have hz : ⁅c, d⁆ ∈ Z := hcm c (hCV hc) d (hDV hd)
    have e : d * c * d⁻¹ = ⁅c, d⁆⁻¹ * c := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact C.mul_mem (C.inv_mem (hZC hz)) hc
  have hnorm : ∀ {C D : Subgroup G}, Z ≤ C → C ≤ V₁ → D ≤ V₂ →
      D ≤ Subgroup.normalizer (C : Set G) := by
    intro C D hZC hCV hDV d hd
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconj hZC hCV hDV d hd c hc, fun hc => ?_⟩
    have h := hconj hZC hCV hDV d⁻¹ (D.inv_mem hd) _ hc
    simpa [mul_assoc] using h
  rintro g ⟨hgA, hgB⟩
  have hA : ((A₁ ⊔ A₂ : Subgroup G) : Set G) = (A₁ : Set G) * (A₂ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A₁ A₂ (hnorm hA₁ hA₁V hA₂V)
  have hB : ((B₁ ⊔ B₂ : Subgroup G) : Set G) = (B₁ : Set G) * (B₂ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left B₁ B₂ (hnorm hB₁ hB₁V hB₂V)
  have hgA' : g ∈ ((A₁ ⊔ A₂ : Subgroup G) : Set G) := hgA
  have hgB' : g ∈ ((B₁ ⊔ B₂ : Subgroup G) : Set G) := hgB
  rw [hA] at hgA'
  rw [hB] at hgB'
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Set.mem_mul.mp hgA'
  obtain ⟨b₁, hb₁, b₂, hb₂, e⟩ := Set.mem_mul.mp hgB'
  have ea : a₁ = b₁ * b₂ * a₂⁻¹ := by rw [e]; group
  have ez : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by rw [ea]; group
  have hz : b₁⁻¹ * a₁ ∈ Z := by
    rw [← hI]
    refine ⟨V₁.mul_mem (V₁.inv_mem (hB₁V hb₁)) (hA₁V ha₁), ?_⟩
    rw [ez]
    exact V₂.mul_mem (hB₂V hb₂) (V₂.inv_mem (hA₂V ha₂))
  have ha₁B : a₁ ∈ B₁ := by
    have : a₁ = b₁ * (b₁⁻¹ * a₁) := by group
    rw [this]
    exact B₁.mul_mem hb₁ (hB₁ hz)
  have ha₂B : a₂ ∈ B₂ := by
    have : a₂ = (b₂ * a₂⁻¹)⁻¹ * b₂ := by group
    rw [this, ← ez]
    exact B₂.mul_mem (B₂.inv_mem (hB₂ hz)) hb₂
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha₁, ha₁B⟩)
    (Subgroup.mem_sup_right ⟨ha₂, ha₂B⟩)

section Assembly

variable {M Q Z B : Subgroup G}

theorem InZClass.mul_self_and_ne (H : StrothHyp M Q Z) {v : G} (h : InZClass Z v) :
    v * v = 1 ∧ v ≠ 1 := by
  obtain ⟨g, z, hz, hz1, rfl⟩ := h
  have hz2 : z * z = 1 := by have := Z_sq H hz; rwa [pow_two] at this
  refine ⟨by rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz2]; group,
    fun h1 => hz1 ?_⟩
  have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
  rw [this, h1]; group

theorem lin213_concl_of (H : StrothHyp M Q Z) {u : G}
    (h : u ^ 2 = 1 ∨ InZClass Z (u ^ 2) ∨ Odd (orderOf u)) :
    (orderOf u = 2 ∨ orderOf u = 4 ∨ Odd (orderOf u)) ∧
      (orderOf u = 4 → InZClass Z (u ^ 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with h | h | h
  · have hd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < orderOf u := Nat.pos_of_dvd_of_pos hd (by norm_num)
    refine ⟨?_, fun h4 => by omega⟩
    interval_cases hk : orderOf u
    · exact Or.inr (Or.inr ⟨0, rfl⟩)
    · exact Or.inl rfl
  · obtain ⟨h2, hne⟩ := InZClass.mul_self_and_ne H h
    have h4 : orderOf u = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · simpa using hne
      · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, pow_two (u ^ 2)]; exact h2
    exact ⟨Or.inr (Or.inl h4), fun _ => h⟩
  · refine ⟨Or.inr (Or.inr h), fun h4 => ?_⟩
    rw [h4] at h
    exact absurd h (by decide)

theorem lin213_concl_conj {u : G} (g : G)
    (h : (orderOf (g * u * g⁻¹) = 2 ∨ orderOf (g * u * g⁻¹) = 4 ∨ Odd (orderOf (g * u * g⁻¹))) ∧
      (orderOf (g * u * g⁻¹) = 4 → InZClass Z ((g * u * g⁻¹) ^ 2))) :
    (orderOf u = 2 ∨ orderOf u = 4 ∨ Odd (orderOf u)) ∧
      (orderOf u = 4 → InZClass Z (u ^ 2)) := by
  have ho : orderOf (g * u * g⁻¹) = orderOf u :=
    orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
  rw [ho] at h
  refine ⟨h.1, fun h4 => ?_⟩
  obtain ⟨a, z, hz, hz1, e⟩ := h.2 h4
  refine ⟨g⁻¹ * a, z, hz, hz1, ?_⟩
  have e' : u ^ 2 = g⁻¹ * (g * u * g⁻¹) ^ 2 * g := by rw [conj_pow]; group
  rw [e', e]; group

theorem sq_eq_one_or_inZClass_of_mem_Q (H : StrothHyp M Q Z) {u : G} (hu : u ∈ Q) :
    u ^ 2 = 1 ∨ InZClass Z (u ^ 2) := by
  by_cases h : u ^ 2 = 1
  · exact Or.inl h
  · exact Or.inr ⟨1, u ^ 2, sq_mem_Z H hu, h, by group⟩

theorem rank_eq_one_of_hasDimOn {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {S V : Subgroup G} {φ : S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (hs : SectionAct K S V Z φ act) (hcard : Nat.card K = Nat.card Z) (hZV : Z ≤ V)
    (hZ2 : 2 ≤ Nat.card Z) {x : G} (hx : x ∈ S) (hD : HasDimOn V Z 1 x) :
    (act (φ ⟨x, hx⟩) - 1).rank = 1 := by
  have hc := card_comm_zpowers_sup_of_sectionAct hs hZV ⟨x, hx⟩
  unfold HasDimOn at hD
  rw [hD, hcard] at hc
  have hq0 : 0 < Nat.card Z := by omega
  have h3 : Nat.card Z ^ (1 + 1) = Nat.card Z * Nat.card Z ^ 1 := by ring
  rw [h3] at hc
  exact (Nat.pow_right_injective hZ2 (Nat.eq_of_mul_eq_mul_left hq0 hc)).symm

theorem isTransvection_of_eq_dihTv {K : Type} [Field K] {n : ℕ} (A : SL(n, K))
    {p r : Fin n → K} (hp : p ≠ 0) (hr : r ≠ 0) (hrp : r ⬝ᵥ p = 0)
    (hA : (A : Matrix (Fin n) (Fin n) K) = dihTv p r) : IsTransvection A := by
  let f : Module.Dual K (Fin n → K) :=
    { toFun := fun v => r ⬝ᵥ v
      map_add' := fun a b => dotProduct_add r a b
      map_smul' := fun c a => by simp [dotProduct_smul] }
  have hfp : f p = 0 := hrp
  refine ⟨fun h1 => ?_, f, p, hfp, LinearEquiv.ext fun x => ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hr
    have e : (A : Matrix (Fin n) (Fin n) K) = 1 := by rw [h1]; rfl
    have h0 : Matrix.vecMulVec p r = 0 := by
      have := hA.symm.trans e
      unfold dihTv at this
      simpa using this
    have := congrFun (congrFun h0 i) j
    simp [Matrix.vecMulVec_apply] at this
    tauto
  · rw [Matrix.SpecialLinearGroup.toLin'_apply, LinearEquiv.transvection.apply, hA,
      Matrix.toLin'_apply, dihTv_mulVec]
    rfl

theorem le_normalizer_of_comm_mem {Z V₁ V₂ C : Subgroup G}
    (hcm : ∀ a ∈ V₁, ∀ b ∈ V₂, ⁅a, b⁆ ∈ Z) (hZC : Z ≤ C) (hCV : C ≤ V₁) :
    V₂ ≤ Subgroup.normalizer (C : Set G) := by
  have hconj : ∀ d ∈ V₂, ∀ c ∈ C, d * c * d⁻¹ ∈ C := by
    intro d hd c hc
    have hz : ⁅c, d⁆ ∈ Z := hcm c (hCV hc) d hd
    have e : d * c * d⁻¹ = ⁅c, d⁆⁻¹ * c := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact C.mul_mem (C.inv_mem (hZC hz)) hc
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => hconj d hd c hc, fun hc => ?_⟩
  have h := hconj d⁻¹ (V₂.inv_mem hd) _ hc
  simpa [mul_assoc] using h

theorem comm_le_sup_comm {Z V₁ V₂ : Subgroup G} {x : G}
    (hcm : ∀ a ∈ V₁, ∀ b ∈ V₂, ⁅a, b⁆ ∈ Z) (hZ₁ : Z ≤ V₁) (hZ₂ : Z ≤ V₂)
    (hx₁ : x ∈ Subgroup.normalizer (V₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    ⁅V₁ ⊔ V₂, Subgroup.zpowers x⁆ ≤
      (⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) ⊔ (⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) := by
  have hcm' : ∀ a ∈ V₂, ∀ b ∈ V₁, ⁅a, b⁆ ∈ Z := fun a ha b hb => by
    have := Z.inv_mem (hcm b hb a ha)
    rwa [commutatorElement_inv] at this
  have hE₂V : ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z ≤ V₂ :=
    comm_sup_le_of_normalizer (S := Subgroup.normalizer (V₂ : Set G)) le_rfl hZ₂ hx₂
  have hV₁N : V₁ ≤ Subgroup.normalizer
      ((⁅V₂, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) : Set G) :=
    le_normalizer_of_comm_mem hcm' le_sup_right hE₂V
  have hmul : ((V₁ ⊔ V₂ : Subgroup G) : Set G) = (V₁ : Set G) * (V₂ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left V₁ V₂
      (le_normalizer_of_comm_mem hcm hZ₁ le_rfl)
  rw [Subgroup.commutator_le]
  intro q hq t ht
  have hq' : q ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := hq
  rw [hmul] at hq'
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Set.mem_mul.mp hq'
  have e : ⁅v₁ * v₂, t⁆ = (v₁ * ⁅v₂, t⁆ * v₁⁻¹) * ⁅v₁, t⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_)
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv₁ ht)))
  exact (Subgroup.mem_normalizer_iff.mp (hV₁N hv₁) _).mp
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv₂ ht))

theorem lin213_caseC (H : StrothHyp M Q Z) {V₁ V₂ : Subgroup G} (hI : V₁ ⊓ V₂ = Z)
    (hU : V₁ ⊔ V₂ = Q) (hZ₁ : Z ≤ V₁) (hZ₂ : Z ≤ V₂) (hV₁Q : V₁ ≤ Q) (hV₂Q : V₂ ≤ Q)
    (h31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) {x y : G}
    (hx₁ : x ∈ Subgroup.normalizer (V₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (V₂ : Set G))
    (hy₁ : y ∈ Subgroup.normalizer (V₁ : Set G)) (hy₂ : y ∈ Subgroup.normalizer (V₂ : Set G))
    (hxx : x * x = 1) (hyy : y * y = 1)
    (hcx : ∃ q ∈ Q, y * x * y⁻¹ = q * x * q⁻¹) (hcy : ∃ q ∈ Q, x * y * x⁻¹ = q * y * q⁻¹)
    (hint : (⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) ⊓ (⁅V₁, Subgroup.zpowers y⁆ ⊔ Z) = Z ∨
      (⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) ⊓ (⁅V₂, Subgroup.zpowers y⁆ ⊔ Z) = Z) :
    (x * y) ^ 2 = 1 ∨ InZClass Z ((x * y) ^ 2) := by
  have hcm : ∀ a ∈ V₁, ∀ b ∈ V₂, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    comm_mem_Z H (hV₁Q ha) (hV₂Q hb)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  obtain ⟨q, hq, hq'⟩ := hcx
  obtain ⟨q', hq'Q, hq''⟩ := hcy
  have hd1 : (x * y) ^ 2 ∈ ⁅Q, Subgroup.zpowers x⁆ := by
    have e : (x * y) ^ 2 = ⁅x, q⁆ := by
      have : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [hyi, pow_two]; group
      rw [this, hq', commutatorElement_def, hxi]; group
    rw [e, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) hq
  have hd2 : (x * y) ^ 2 ∈ ⁅Q, Subgroup.zpowers y⁆ := by
    have e : (x * y) ^ 2 = (⁅y, q'⁆)⁻¹ := by
      have : (y * x) ^ 2 = y * (x * y * x⁻¹) := by rw [hxi, pow_two]; group
      have e2 : (y * x) ^ 2 = ⁅y, q'⁆ := by
        rw [this, hq'', commutatorElement_def, hyi]; group
      rw [← e2]; simp [pow_two, mul_inv_rev, hxi, hyi, mul_assoc]
    rw [e]
    refine Subgroup.inv_mem _ ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers y) hq'Q
  rw [← hU] at hd1 hd2
  have hb1 := comm_le_sup_comm hcm hZ₁ hZ₂ hx₁ hx₂ hd1
  have hb2 := comm_le_sup_comm hcm hZ₁ hZ₂ hy₁ hy₂ hd2
  have hEle : ∀ {V : Subgroup G} {t : G}, Z ≤ V → t ∈ Subgroup.normalizer (V : Set G) →
      ⁅V, Subgroup.zpowers t⁆ ⊔ Z ≤ V := fun hZV ht =>
    comm_sup_le_of_normalizer (S := Subgroup.normalizer _) le_rfl hZV ht
  have hdec := sup_inf_sup_le hI le_sup_right (hEle hZ₁ hx₁) le_sup_right (hEle hZ₂ hx₂)
    le_sup_right (hEle hZ₁ hy₁) le_sup_right (hEle hZ₂ hy₂) hcm ⟨hb1, hb2⟩
  have hdQ : (x * y) ^ 2 ∈ V₁ ∨ (x * y) ^ 2 ∈ V₂ := by
    rcases hint with h | h
    · rw [h] at hdec
      exact Or.inr ((sup_le hZ₂ (inf_le_left.trans (hEle hZ₂ hx₂))) hdec)
    · rw [h] at hdec
      exact Or.inl ((sup_le (inf_le_left.trans (hEle hZ₁ hx₁)) hZ₁) hdec)
  by_cases h1 : (x * y) ^ 2 = 1
  · exact Or.inl h1
  · refine Or.inr ((h31 _ ?_ h1).mpr hdQ)
    rcases hdQ with h | h
    · exact hV₁Q h
    · exact hV₂Q h

@[expose] noncomputable def phiSL {n : ℕ} {K : Type} [Field K] {L : Subgroup G}
    (φ : L →* GL (Fin n) K)
    (hr : φ.range = StatedSL n K) : L →* SL(n, K) where
  toFun g := ⟨(φ g : Matrix (Fin n) (Fin n) K),
    CFSG.Open.StatedAPI.det_of_mem_statedSL (by rw [← hr]; exact ⟨g, rfl⟩)⟩
  map_one' := by ext; simp
  map_mul' a b := Subtype.ext (show ((φ (a * b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    (φ a : Matrix (Fin n) (Fin n) K) * (φ b : Matrix (Fin n) (Fin n) K) by simp)

@[simp] theorem coe_phiSL {n : ℕ} {K : Type} [Field K] {L : Subgroup G} (φ : L →* GL (Fin n) K)
    (hr : φ.range = StatedSL n K) (g : L) :
    ((phiSL φ hr g : SL(n, K)) : Matrix (Fin n) (Fin n) K) = (φ g : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem phiSL_surjective {n : ℕ} {K : Type} [Field K] {L : Subgroup G} (φ : L →* GL (Fin n) K)
    (hr : φ.range = StatedSL n K) : Function.Surjective (phiSL φ hr) := by
  intro A
  have hA : (Matrix.SpecialLinearGroup.toGL A : GL (Fin n) K) ∈ φ.range := by
    rw [hr, CFSG.Open.StatedAPI.statedSL_eq_range_toGL]; exact ⟨A, rfl⟩
  obtain ⟨g, hg⟩ := hA
  refine ⟨g, ?_⟩
  ext i j
  simp [hg]

theorem phi_eq_of_phiSL_eq {n : ℕ} {K : Type} [Field K] {L : Subgroup G} {φ : L →* GL (Fin n) K}
    {hr : φ.range = StatedSL n K} {a b : L} (h : phiSL φ hr a = phiSL φ hr b) : φ a = φ b := by
  ext i j
  have := congrArg (fun A : SL(n, K) => (A : Matrix (Fin n) (Fin n) K) i j) h
  simpa using this

theorem eq_of_phi_eq {n : ℕ} {K : Type} [Field K] {Q L C : Subgroup G} {φ : L →* GL (Fin n) K}
    (hker : φ.ker = Q.subgroupOf L) (hCQ : C ⊓ Q = ⊥) {a b : G} (haC : a ∈ C) (hbC : b ∈ C)
    (haL : a ∈ L) (hbL : b ∈ L) (h : φ ⟨a, haL⟩ = φ ⟨b, hbL⟩) : a = b := by
  have hk : (⟨a, haL⟩ : L)⁻¹ * ⟨b, hbL⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have hm : a⁻¹ * b ∈ C ⊓ Q := ⟨C.mul_mem (C.inv_mem haC) hbC, hk⟩
  rw [hCQ, Subgroup.mem_bot] at hm
  exact (inv_mul_eq_one.mp hm)

theorem exists_mul_of_compl {M Q C : Subgroup G} (hn : M ≤ Subgroup.normalizer (Q : Set G))
    (hCM : C ≤ M) (hCQM : C ⊔ Q = M) {g : G} (hg : g ∈ M) : ∃ k ∈ C, ∃ w ∈ Q, g = k * w := by
  have hmul : ((C ⊔ Q : Subgroup G) : Set G) = (C : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C Q (hCM.trans hn)
  have hg' : g ∈ ((C ⊔ Q : Subgroup G) : Set G) := by rw [hCQM]; exact hg
  rw [hmul] at hg'
  obtain ⟨k, hk, w, hw, rfl⟩ := Set.mem_mul.mp hg'
  exact ⟨k, hk, w, hw, rfl⟩

theorem inZClass_of_compl {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {M Q Z L C : Subgroup G} (φ : L →* GL (Fin n) K) (hr : φ.range = StatedSL n K)
    (hker : φ.ker = Q.subgroupOf L) (hQL : Q ≤ L) (hLM : L ≤ M)
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) (hQn : M ≤ Subgroup.normalizer (Q : Set G))
    (hCM : C ≤ M) (hCQ : C ⊓ Q = ⊥) (hCQM : C ⊔ Q = M)
    {x : G} (hxC : x ∈ C) (hxL : x ∈ L) (hx : InZClass Z x)
    (htx : IsTransvection (phiSL φ hr ⟨x, hxL⟩))
    {s : G} (hsC : s ∈ C) (hsL : s ∈ L) (hts : IsTransvection (phiSL φ hr ⟨s, hsL⟩)) :
    InZClass Z s := by
  obtain ⟨W, hW⟩ := transv_conj_SL htx hts
  obtain ⟨g, rfl⟩ := phiSL_surjective φ hr W
  obtain ⟨k, hkC, w, hwQ, hgkw⟩ := exists_mul_of_compl hQn hCM hCQM (hLM g.2)
  have hkL : k ∈ L := by
    have : k = (g : G) * w⁻¹ := by rw [hgkw]; group
    rw [this]; exact L.mul_mem g.2 (L.inv_mem (hQL hwQ))
  have hwk : (⟨w, hQL hwQ⟩ : L) ∈ φ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]; exact hwQ
  have hg : g = ⟨k, hkL⟩ * ⟨w, hQL hwQ⟩ := Subtype.ext hgkw
  have hgk : phiSL φ hr g = phiSL φ hr ⟨k, hkL⟩ := by
    have h1 : phiSL φ hr ⟨w, hQL hwQ⟩ = 1 := by
      ext i j
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j)
        (MonoidHom.mem_ker.mp hwk)
      simpa using this
    rw [hg, map_mul, h1, mul_one]
  have hs'L : k * x * k⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hLn (hCM hkC)) x).mp hxL
  have hs'C : k * x * k⁻¹ ∈ C := C.mul_mem (C.mul_mem hkC hxC) (C.inv_mem hkC)
  have he : (⟨k * x * k⁻¹, hs'L⟩ : L) = ⟨k, hkL⟩ * ⟨x, hxL⟩ * (⟨k, hkL⟩ : L)⁻¹ := rfl
  have hφ : φ ⟨k * x * k⁻¹, hs'L⟩ = φ ⟨s, hsL⟩ := by
    apply phi_eq_of_phiSL_eq (hr := hr)
    rw [← hW, hgk, he, map_mul, map_mul, map_inv]
  have hs : k * x * k⁻¹ = s := eq_of_phi_eq hker hCQ hs'C hsC hs'L hsL hφ
  rw [← hs]
  obtain ⟨a, z, hz, hz1, rfl⟩ := hx
  exact ⟨k * a, z, hz, hz1, by group⟩

theorem sub_one_mul_self {K : Type} [Field K] [CharP K 2] {n : ℕ} {P : Matrix (Fin n) (Fin n) K}
    (h : P * P = 1) : (P - 1) * (P - 1) = 0 := by
  have h2 : ∀ A : Matrix (Fin n) (Fin n) K, A + A = 0 := fun A => by
    ext i j; simp [CharTwo.add_self_eq_zero]
  calc (P - 1) * (P - 1) = P * P - P - P + 1 := by noncomm_ring
    _ = (1 + 1) - (P + P) := by rw [h]; abel
    _ = 0 := by rw [h2 1, h2 P, sub_zero]

theorem commute_of_sub_one {K : Type} [Field K] [CharP K 2] {n : ℕ}
    {P R : Matrix (Fin n) (Fin n) K} (hP : P * P = 1) (hR : R * R = 1)
    (h : LinearMap.range (P - 1).mulVecLin = LinearMap.range (R - 1).mulVecLin ∨
      LinearMap.ker (P - 1).mulVecLin = LinearMap.ker (R - 1).mulVecLin) :
    P * R = R * P := by
  obtain ⟨h12, h21⟩ := sqZero_mul_eq_zero (sub_one_mul_self hP) (sub_one_mul_self hR) h
  calc P * R = (P - 1) * (R - 1) + (P - 1) + (R - 1) + 1 := by noncomm_ring
    _ = (R - 1) * (P - 1) + (R - 1) + (P - 1) + 1 := by rw [h12, h21]; abel
    _ = R * P := by noncomm_ring

theorem mem_CQt_of_comm {Q Z : Subgroup G} {x a : G} (hx : x * x = 1) (ha : a ∈ Q)
    (h : ⁅x, a⁆ ∈ Z) : a ∈ CQt Q Z (Subgroup.zpowers x) := by
  refine ⟨ha, fun t ht => ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers hx ht with rfl | rfl
  · simp [commutatorElement_def, Z.one_mem]
  · exact h

theorem exists_sit {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {t : G} (ht : InZClass Z t)
    (hM : t ∈ M) (hQ : t ∉ Q) : ∃ X : Subgroup G, Sit M Q Z X t := by
  obtain ⟨g, z, hz, hz1, rfl⟩ := ht
  exact ⟨_, Sit.of_conj H hz hz1 hM hQ⟩

theorem Sit.comm_of_mem_Z {M Q Z X : Subgroup G} {x : G} (hs : Sit M Q Z X x) {z : G}
    (hz : z ∈ Z) : x * z = z * x :=
  (Sit.inf_QB_sup_Z_comm hs).2 z (Subgroup.mem_sup_right hz)

theorem isTransvection_phiSL {n : ℕ} {K : Type} [Field K] {L : Subgroup G}
    (φ : L →* GL (Fin n) K) (hr : φ.range = StatedSL n K) (t : L)
    (h : ((φ t : Matrix (Fin n) (Fin n) K) - 1).rank = 1) : IsTransvection (phiSL φ hr t) := by
  obtain ⟨p, r, hp, hr0, hrp, he⟩ := exists_eq_dihTv_of_rank_eq_one h (phiSL φ hr t).2
  exact isTransvection_of_eq_dihTv _ hp hr0 hrp he

theorem orderOf_mul_eq_of_compl {n : ℕ} {K : Type} [Field K] {Q L C : Subgroup G}
    (φ : L →* GL (Fin n) K) (hr : φ.range = StatedSL n K) (hker : φ.ker = Q.subgroupOf L)
    (hCQ : C ⊓ Q = ⊥) {a : G} (haC : a ∈ C) (haL : a ∈ L) :
    orderOf a = orderOf (phiSL φ hr ⟨a, haL⟩) := by
  let f : ↥(C ⊓ L) →* SL(n, K) := (phiSL φ hr).comp (Subgroup.inclusion inf_le_right)
  have hf : Function.Injective f := by
    intro u w h
    apply Subtype.ext
    exact eq_of_phi_eq hker hCQ u.2.1 w.2.1 u.2.2 w.2.2 (phi_eq_of_phiSL_eq (hr := hr) h)
  have h1 := orderOf_injective f hf ⟨a, haC, haL⟩
  have h2 : orderOf a = orderOf (⟨a, haC, haL⟩ : ↥(C ⊓ L)) :=
    Subgroup.orderOf_coe (⟨a, haC, haL⟩ : ↥(C ⊓ L))
  rw [h2, ← h1]
  rfl

theorem exists_conj_of_inZClass' {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {u v : G}
    (hu : InZClass Z u) (hv : InZClass Z v) : ∃ g : G, g * u * g⁻¹ = v := by
  obtain ⟨a, z₁, hz₁, hz₁1, rfl⟩ := hu
  obtain ⟨b, z₂, hz₂, hz₂1, rfl⟩ := hv
  obtain ⟨m, -, hm⟩ := Z_isConj H hz₁ hz₁1 hz₂ hz₂1
  refine ⟨b * m * a⁻¹, ?_⟩
  calc b * m * a⁻¹ * (a * z₁ * a⁻¹) * (b * m * a⁻¹)⁻¹ = b * (m * z₁ * m⁻¹) * b⁻¹ := by group
    _ = b * z₂ * b⁻¹ := by rw [hm]

theorem phi_eq_one_of_mem {n : ℕ} {K : Type} [Field K] {Q L : Subgroup G}
    {φ : L →* GL (Fin n) K} (hker : φ.ker = Q.subgroupOf L) {w : G} (hw : w ∈ Q) (hwL : w ∈ L) :
    φ ⟨w, hwL⟩ = 1 := by
  have : (⟨w, hwL⟩ : L) ∈ φ.ker := by rw [hker, Subgroup.mem_subgroupOf]; exact hw
  exact this

theorem lin213_of_compl {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {M Q Z L C : Subgroup G} (H : StrothHyp M Q Z) (φ : L →* GL (Fin n) K)
    (hr : φ.range = StatedSL n K) (hker : φ.ker = Q.subgroupOf L) (hQL : Q ≤ L) (hLM : L ≤ M)
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) (hQn : M ≤ Subgroup.normalizer (Q : Set G))
    (hCM : C ≤ M) (hCQ : C ⊓ Q = ⊥) (hCQM : C ⊔ Q = M)
    {x y : G} (hxC : x ∈ C) (hyC : y ∈ C) (hxL : x ∈ L) (hyL : y ∈ L) (hx : InZClass Z x)
    (htx : IsTransvection (phiSL φ hr ⟨x, hxL⟩)) (hty : IsTransvection (phiSL φ hr ⟨y, hyL⟩))
    (hne : φ ⟨x, hxL⟩ ≠ φ ⟨y, hyL⟩) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  have hne' : phiSL φ hr ⟨x, hxL⟩ ≠ phiSL φ hr ⟨y, hyL⟩ := fun h =>
    hne (phi_eq_of_phiSL_eq h)
  have ho := orderOf_mul_eq_of_compl φ hr hker hCQ (C.mul_mem hxC hyC) (L.mul_mem hxL hyL)
  have hm : phiSL φ hr ⟨x * y, L.mul_mem hxL hyL⟩ =
      phiSL φ hr ⟨x, hxL⟩ * phiSL φ hr ⟨y, hyL⟩ := by
    rw [← map_mul]; rfl
  rw [hm] at ho
  apply lin213_concl_of H
  rcases transv_mul_orderOf htx hty hne' with h | ⟨-, ht⟩ | h
  · left
    rw [← ho] at h
    rw [← h]
    exact pow_orderOf_eq_one _
  · right; left
    have hsC : (x * y) ^ 2 ∈ C := C.pow_mem (C.mul_mem hxC hyC) 2
    have hsL : (x * y) ^ 2 ∈ L := L.pow_mem (L.mul_mem hxL hyL) 2
    have hs : phiSL φ hr ⟨(x * y) ^ 2, hsL⟩ = (phiSL φ hr ⟨x, hxL⟩ * phiSL φ hr ⟨y, hyL⟩) ^ 2 := by
      rw [← hm, ← map_pow]; rfl
    exact inZClass_of_compl φ hr hker hQL hLM hLn hQn hCM hCQ hCQM hxC hxL hx htx hsC hsL
      (by rw [hs]; exact ht)
  · right; right
    rwa [ho]

theorem exists_compl_rep {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {M Q Z B V₁ V₂ C : Subgroup G} (H : StrothHyp M Q Z) (h212 : Lin212Prop M Q Z B V₁ V₂)
    (φ : Lgen M (LB M Q B) →* GL (Fin n) K)
    (hr : φ.range = StatedSL n K) (hker : φ.ker = Q.subgroupOf (Lgen M (LB M Q B)))
    (hQL : Q ≤ Lgen M (LB M Q B)) (hLM : Lgen M (LB M Q B) ≤ M)
    (hLn : M ≤ Subgroup.normalizer (Lgen M (LB M Q B) : Set G))
    (hQn : M ≤ Subgroup.normalizer (Q : Set G))
    (hCM : C ≤ M) (hCQ : C ⊓ Q = ⊥) (hCQM : C ⊔ Q = M)
    {x : G} (hxC : x ∈ C) (hxL : x ∈ Lgen M (LB M Q B)) (hx : InZClass Z x)
    (htx : IsTransvection (phiSL φ hr ⟨x, hxL⟩))
    {y : G} (hyM : y ∈ M) (hy : InZClass Z y) (hyQ : y ∉ Q) (hyL : y ∈ Lgen M (LB M Q B))
    (hty : IsTransvection (phiSL φ hr ⟨y, hyL⟩)) :
    ∃ y₀ ∈ C, ∃ hy₀L : y₀ ∈ Lgen M (LB M Q B), InZClass Z y₀ ∧ y₀ ∉ Q ∧
      φ ⟨y₀, hy₀L⟩ = φ ⟨y, hyL⟩ ∧ ∃ v ∈ Q, y = v * y₀ * v⁻¹ := by
  obtain ⟨k, hkC, w, hwQ, hykw⟩ := exists_mul_of_compl hQn hCM hCQM hyM
  have hkL : k ∈ Lgen M (LB M Q B) := by
    have : k = y * w⁻¹ := by rw [hykw]; group
    rw [this]; exact Subgroup.mul_mem _ hyL (Subgroup.inv_mem _ (hQL hwQ))
  have hφ : φ ⟨k, hkL⟩ = φ ⟨y, hyL⟩ := by
    have e : (⟨y, hyL⟩ : Lgen M (LB M Q B)) = ⟨k, hkL⟩ * ⟨w, hQL hwQ⟩ := Subtype.ext hykw
    rw [e, map_mul, phi_eq_one_of_mem hker hwQ, mul_one]
  have htk : IsTransvection (phiSL φ hr ⟨k, hkL⟩) := by
    have : phiSL φ hr ⟨k, hkL⟩ = phiSL φ hr ⟨y, hyL⟩ := by
      ext i j; simp [hφ]
    rw [this]; exact hty
  have hk := inZClass_of_compl φ hr hker hQL hLM hLn hQn hCM hCQ hCQM hxC hxL hx htx hkC hkL htk
  have hkQ : k ∉ Q := fun h => hyQ (by rw [hykw]; exact Q.mul_mem h hwQ)
  obtain ⟨X₀, hs⟩ := exists_sit H hk (hCM hkC) hkQ
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := h212 X₀ k hs
  obtain ⟨g, hg⟩ := exists_conj_of_inZClass' H hk hy
  obtain ⟨v, hv, hv'⟩ := h7 g w hwQ (by rw [hg, hykw])
  exact ⟨k, hkC, hkL, hk, hkQ, hφ, v, hv, by rw [← hv', hg]⟩

theorem phi_mat_mul_self {n : ℕ} {K : Type} [Field K] {L : Subgroup G} (φ : L →* GL (Fin n) K)
    (t : L) (ht : (t : G) * t = 1) :
    (φ t : Matrix (Fin n) (Fin n) K) * (φ t : Matrix (Fin n) (Fin n) K) = 1 := by
  have h : φ t * φ t = 1 := by
    rw [← map_mul, show t * t = 1 from Subtype.ext ht, map_one]
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
  simpa using this

theorem phi_inv_of_mul_self {n : ℕ} {K : Type} [Field K] {L : Subgroup G} (φ : L →* GL (Fin n) K)
    (t : L) (ht : (t : G) * t = 1) : (φ t)⁻¹ = φ t := by
  rw [← map_inv]
  congr 1
  exact Subtype.ext (inv_eq_of_mul_eq_one_right ht)

theorem lin213_core {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {M Q Z B V₁ V₂ C : Subgroup G} (hc : Ctx M Q Z B) (h212 : Lin212Prop M Q Z B V₁ V₂)
    (hcard : Nat.card K = Nat.card Z)
    (φ : Lgen M (LB M Q B) →* GL (Fin n) K) (hr : φ.range = StatedSL n K)
    (hker : φ.ker = Q.subgroupOf (Lgen M (LB M Q B)))
    (hZ₁ : Z ≤ V₁) (hV₁Q : V₁ ≤ Q) (hZ₂ : Z ≤ V₂) (hV₂Q : V₂ ≤ Q) (hI : V₁ ⊓ V₂ = Z)
    (hU : V₁ ⊔ V₂ = Q)
    (hs₁ : SectionAct (ι := Fin n) K (Lgen M (LB M Q B)) V₁ Z φ
      (fun g => (g : Matrix (Fin n) (Fin n) K)))
    (hs₂ : SectionAct (ι := Fin n) K (Lgen M (LB M Q B)) V₂ Z φ
      (fun g => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ))
    (h31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂))
    (hCM : C ≤ M) (hCQ : C ⊓ Q = ⊥) (hCQM : C ⊔ Q = M)
    {x y : G} (hxC : x ∈ C) (hxM : x ∈ M) (hyM : y ∈ M) (hx : InZClass Z x)
    (hy : InZClass Z y) (hxQ : x ∉ Q) (hyQ : y ∉ Q) (hxyQ : x * y ∉ Q) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  have H := hc.hyp
  have hQL : Q ≤ Lgen M (LB M Q B) := hc.Q_le_Lgen
  have hLM : Lgen M (LB M Q B) ≤ M := hc.Lgen_le_M
  have hLn := Lgen_normalizes M (LB M Q B)
  have hQn := cqt_M_le_normalizer_Q H
  have hZ2 : 2 ≤ Nat.card Z := by have := H.q4; omega
  have hcm : ∀ a ∈ V₁, ∀ b ∈ V₂, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    comm_mem_Z H (hV₁Q ha) (hV₂Q hb)
  obtain ⟨X, hsx⟩ := exists_sit H hx hxM hxQ
  obtain ⟨Y, hsy⟩ := exists_sit H hy hyM hyQ
  obtain ⟨hxL, hx1, hx2, -, hx5, hx6, hx7, -⟩ := h212 X x hsx
  obtain ⟨hyL, hy1, hy2, -, -, -, hy7, -⟩ := h212 Y y hsy
  have hxx := (InZClass.mul_self_and_ne H hx).1
  have hyy := (InZClass.mul_self_and_ne H hy).1
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have rx1 : ((φ ⟨x, hxL⟩ : Matrix (Fin n) (Fin n) K) - 1).rank = 1 :=
    rank_eq_one_of_hasDimOn hs₁ hcard hZ₁ hZ2 hxL hx1
  have ry1 : ((φ ⟨y, hyL⟩ : Matrix (Fin n) (Fin n) K) - 1).rank = 1 :=
    rank_eq_one_of_hasDimOn hs₁ hcard hZ₁ hZ2 hyL hy1
  have rx2 : ((((φ ⟨x, hxL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).rank = 1 :=
    rank_eq_one_of_hasDimOn hs₂ hcard hZ₂ hZ2 hxL hx2
  have ry2 : ((((φ ⟨y, hyL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).rank = 1 :=
    rank_eq_one_of_hasDimOn hs₂ hcard hZ₂ hZ2 hyL hy2
  have htx := isTransvection_phiSL φ hr ⟨x, hxL⟩ rx1
  have hty := isTransvection_phiSL φ hr ⟨y, hyL⟩ ry1
  have hne : φ ⟨x, hxL⟩ ≠ φ ⟨y, hyL⟩ := by
    intro h
    apply hxyQ
    have hk : (⟨x, hxL⟩ : Lgen M (LB M Q B))⁻¹ * ⟨y, hyL⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    have e : x * y = x⁻¹ * y := by rw [hxi]
    rw [e]; exact hk
  have hPx := phi_mat_mul_self φ ⟨x, hxL⟩ hxx
  have hPy := phi_mat_mul_self φ ⟨y, hyL⟩ hyy
  have hix := phi_inv_of_mul_self φ ⟨x, hxL⟩ hxx
  have hiy := phi_inv_of_mul_self φ ⟨y, hyL⟩ hyy
  by_cases hK : LinearMap.ker ((φ ⟨x, hxL⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin =
      LinearMap.ker ((φ ⟨y, hyL⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin ∨
    LinearMap.ker ((((φ ⟨x, hxL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin =
      LinearMap.ker ((((φ ⟨y, hyL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin
  ·
    have hcomm : (φ ⟨x, hxL⟩ : Matrix (Fin n) (Fin n) K) * (φ ⟨y, hyL⟩ : Matrix (Fin n) (Fin n) K) =
        (φ ⟨y, hyL⟩ : Matrix (Fin n) (Fin n) K) * (φ ⟨x, hxL⟩ : Matrix (Fin n) (Fin n) K) := by
      rcases hK with h | h
      · exact commute_of_sub_one hPx hPy (Or.inr h)
      · rw [hix, hiy] at h
        have hT : ∀ P : Matrix (Fin n) (Fin n) K, P * P = 1 → Pᵀ * Pᵀ = 1 := fun P hP => by
          rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
        have := commute_of_sub_one (hT _ hPx) (hT _ hPy) (Or.inr h)
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul] at this
        exact (Matrix.transpose_injective this).symm
    have hcommGL : φ ⟨x, hxL⟩ * φ ⟨y, hyL⟩ = φ ⟨y, hyL⟩ * φ ⟨x, hxL⟩ := Units.ext hcomm
    by_cases hR : LinearMap.range ((φ ⟨x, hxL⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin =
        LinearMap.range ((φ ⟨y, hyL⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin ∧
      LinearMap.range
          ((((φ ⟨x, hxL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin =
        LinearMap.range
          ((((φ ⟨y, hyL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin
    ·
      obtain ⟨hR1, hR2⟩ := hR
      apply lin213_concl_of H
      left
      obtain ⟨y₀, hy₀C, hy₀L, hy₀, hy₀Q, hφ0, v, hvQ, hyv⟩ := exists_compl_rep H h212 φ hr hker
        hQL hLM hLn hQn hCM hCQ hCQM hxC hxL hx htx hyM hy hyQ hyL hty
      have hy₀y₀ := (InZClass.mul_self_and_ne H hy₀).1
      have hy₀i : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right hy₀y₀
      have hxy0 : x * y₀ = y₀ * x := by
        refine eq_of_phi_eq hker hCQ (C.mul_mem hxC hy₀C) (C.mul_mem hy₀C hxC)
          (Subgroup.mul_mem _ hxL hy₀L) (Subgroup.mul_mem _ hy₀L hxL) ?_
        change φ (⟨x, hxL⟩ * ⟨y₀, hy₀L⟩) = φ (⟨y₀, hy₀L⟩ * ⟨x, hxL⟩)
        rw [map_mul, map_mul, hφ0, hcommGL]
      have he : y₀ * y = ⁅v, y₀⁆⁻¹ := by
        rw [hyv, commutatorElement_def]
        simp only [mul_inv_rev, inv_inv, hy₀i]
        group
      have heQ : y₀ * y ∈ ⁅Q, Subgroup.zpowers y₀⁆ := by
        rw [he]
        exact Subgroup.inv_mem _
          (Subgroup.commutator_mem_commutator hvQ (Subgroup.mem_zpowers y₀))
      obtain ⟨Y₀, hsy0⟩ := exists_sit H hy₀ (hCM hy₀C) hy₀Q
      obtain ⟨-, -, -, -, hy05, -⟩ := h212 Y₀ y₀ hsy0
      have hA0 := Sit.inf_QB_sup_Z_comm hsy0
      have hAx := Sit.inf_QB_sup_Z_comm hsx
      have he0 : y₀ * y ∈ (Q ⊓ QB Y₀) ⊔ Z := by
        rw [hy05]; exact Subgroup.mem_sup_left heQ
      have hex : y₀ * y ∈ (Q ⊓ QB X) ⊔ Z := by
        rw [hx5]
        have h1 : y₀ * y ∈ ⁅V₁ ⊔ V₂, Subgroup.zpowers y₀⁆ := by rw [hU]; exact heQ
        have h2 := comm_le_sup_comm hcm hZ₁ hZ₂ (hs₁.1 hy₀L) (hs₂.1 hy₀L) h1
        have e1 := SectionAct.comm_sup_eq_of_range_eq hs₁ hZ₁ (s := ⟨y₀, hy₀L⟩) (t := ⟨x, hxL⟩)
          hy₀y₀ hxx (by rw [hφ0]; exact hR1.symm)
        have e2 := SectionAct.comm_sup_eq_of_range_eq hs₂ hZ₂ (s := ⟨y₀, hy₀L⟩) (t := ⟨x, hxL⟩)
          hy₀y₀ hxx (by rw [hφ0]; exact hR2.symm)
        simp only at e1 e2
        rw [e1, e2] at h2
        have hle : (⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) ⊔ (⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) ≤
            ⁅Q, Subgroup.zpowers x⁆ ⊔ Z :=
          sup_le (sup_le (le_sup_of_le_left (Subgroup.commutator_mono hV₁Q le_rfl)) le_sup_right)
            (sup_le (le_sup_of_le_left (Subgroup.commutator_mono hV₂Q le_rfl)) le_sup_right)
        exact hle h2
      set e := y₀ * y with he_def
      have hye : y = y₀ * e := by
        rw [he_def, ← mul_assoc, hy₀y₀, one_mul]
      have c1 : Commute x y₀ := hxy0
      have c2 : Commute x e := hAx.2 e hex
      have c3 : Commute y₀ e := hA0.2 e he0
      have hee : e ^ 2 = 1 := hA0.1.2 e he0
      rw [hye, ← mul_assoc, (c2.mul_left c3).mul_pow, c1.mul_pow, hee, pow_two x, hxx,
        pow_two y₀, hy₀y₀]
      simp
    ·
      apply lin213_concl_of H
      have hcx : ∃ q ∈ Q, y * x * y⁻¹ = q * x * q⁻¹ := by
        refine hx7 y (x⁻¹ * (y * x * y⁻¹)) ?_ (by group)
        have hk : (⟨x, hxL⟩ : Lgen M (LB M Q B))⁻¹ *
            (⟨y, hyL⟩ * ⟨x, hxL⟩ * (⟨y, hyL⟩ : Lgen M (LB M Q B))⁻¹) ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcommGL]
          group
        rw [hker, Subgroup.mem_subgroupOf] at hk
        exact hk
      have hcy : ∃ q ∈ Q, x * y * x⁻¹ = q * y * q⁻¹ := by
        refine hy7 x (y⁻¹ * (x * y * x⁻¹)) ?_ (by group)
        have hk : (⟨y, hyL⟩ : Lgen M (LB M Q B))⁻¹ *
            (⟨x, hxL⟩ * ⟨y, hyL⟩ * (⟨x, hxL⟩ : Lgen M (LB M Q B))⁻¹) ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcommGL]
          group
        rw [hker, Subgroup.mem_subgroupOf] at hk
        exact hk
      have hint : (⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) ⊓ (⁅V₁, Subgroup.zpowers y⁆ ⊔ Z) = Z ∨
          (⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) ⊓ (⁅V₂, Subgroup.zpowers y⁆ ⊔ Z) = Z := by
        by_cases hR1 : LinearMap.range ((φ ⟨x, hxL⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin =
            LinearMap.range ((φ ⟨y, hyL⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin
        · have hR2 := fun h => hR ⟨hR1, h⟩
          right
          exact SectionAct.comm_sup_inf_eq hs₂ hZ₂ (s := ⟨x, hxL⟩) (t := ⟨y, hyL⟩) hxx hyy
            (range_inf_range_eq_bot rx2 ry2 hR2)
        · left
          exact SectionAct.comm_sup_inf_eq hs₁ hZ₁ (s := ⟨x, hxL⟩) (t := ⟨y, hyL⟩) hxx hyy
            (range_inf_range_eq_bot rx1 ry1 hR1)
      rcases lin213_caseC H hI hU hZ₁ hZ₂ hV₁Q hV₂Q h31 (hs₁.1 hxL) (hs₂.1 hxL) (hs₁.1 hyL)
        (hs₂.1 hyL) hxx hyy hcx hcy hint with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  ·
    push_neg at hK
    obtain ⟨hK1, hK2⟩ := hK
    obtain ⟨y₀, hy₀C, hy₀L, hy₀, hy₀Q, hφ0, v, hvQ, hyv⟩ := exists_compl_rep H h212 φ hr hker
      hQL hLM hLn hQn hCM hCQ hCQM hxC hxL hx htx hyM hy hyQ hyL hty
    have hy₀y₀ := (InZClass.mul_self_and_ne H hy₀).1
    obtain ⟨Y₀, hsy0⟩ := exists_sit H hy₀ (hCM hy₀C) hy₀Q
    obtain ⟨-, -, -, -, -, hy06, -⟩ := h212 Y₀ y₀ hsy0
    have hk1 : LinearMap.ker ((φ ⟨x, hxL⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin ⊔
        LinearMap.ker ((φ ⟨y₀, hy₀L⟩ : Matrix (Fin n) (Fin n) K) - 1).mulVecLin = ⊤ := by
      rw [hφ0]; exact ker_sup_ker_eq_top rx1 ry1 hK1
    have hk2 : LinearMap.ker
          ((((φ ⟨x, hxL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin ⊔
        LinearMap.ker
          ((((φ ⟨y₀, hy₀L⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).mulVecLin = ⊤ := by
      rw [hφ0]; exact ker_sup_ker_eq_top rx2 ry2 hK2
    have hcm' : ∀ a ∈ V₂, ∀ b ∈ V₁, ⁅a, b⁆ ∈ Z := fun a ha b hb => by
      have := Z.inv_mem (hcm b hb a ha)
      rwa [commutatorElement_inv] at this
    have hmul : ((V₁ ⊔ V₂ : Subgroup G) : Set G) = (V₁ : Set G) * (V₂ : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ (le_normalizer_of_comm_mem hcm' hZ₂ le_rfl)
    have hv' : v ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by rw [hU]; exact hvQ
    rw [hmul] at hv'
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := Set.mem_mul.mp hv'
    obtain ⟨c₁, hc₁, c₁', hc₁', e₁, hz₁, hz₁'⟩ :=
      SectionAct.exists_mul_of_ker_sup hs₁ (s := ⟨x, hxL⟩) (t := ⟨y₀, hy₀L⟩) hk1 hv₁
    obtain ⟨c₂, hc₂, c₂', hc₂', e₂, hz₂, hz₂'⟩ :=
      SectionAct.exists_mul_of_ker_sup hs₂ (s := ⟨x, hxL⟩) (t := ⟨y₀, hy₀L⟩) hk2 hv₂
    simp only at hz₁ hz₁' hz₂ hz₂'
    have hZQ : Z ≤ Q := hZ₁.trans hV₁Q
    have hcC : c₁ * c₂ ∈ CQt Q Z (Subgroup.zpowers x) :=
      (CQtGrp hc (Subgroup.zpowers x)).mul_mem (mem_CQt_of_comm hxx (hV₁Q hc₁) hz₁)
        (mem_CQt_of_comm hxx (hV₂Q hc₂) hz₂)
    rw [hx6] at hcC
    have hcx : x * (c₁ * c₂) = (c₁ * c₂) * x := by
      have hle : (Q ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ Z ≤
          Subgroup.centralizer ({x} : Set G) :=
        sup_le inf_le_right fun z hz =>
          Subgroup.mem_centralizer_iff.mpr fun t ht => by
            rw [Set.mem_singleton_iff.mp ht]; exact Sit.comm_of_mem_Z hsx hz
      exact Subgroup.mem_centralizer_iff.mp (hle hcC) x (Set.mem_singleton x)
    have hZC0 : ∀ z ∈ Z, z ∈ CQt Q Z (Subgroup.zpowers y₀) := fun z hz =>
      mem_CQt_of_comm hy₀y₀ (hZQ hz) (by
        rw [commutatorElement_def, Sit.comm_of_mem_Z hsy0 hz]; group; exact Z.one_mem)
    have hconj : c₂⁻¹ * c₁' * c₂ ∈ CQt Q Z (Subgroup.zpowers y₀) := by
      have e : c₂⁻¹ * c₁' * c₂ = c₁' * ⁅c₁'⁻¹, c₂⁻¹⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact (CQtGrp hc (Subgroup.zpowers y₀)).mul_mem
        (mem_CQt_of_comm hy₀y₀ (hV₁Q hc₁') hz₁')
        (hZC0 _ (comm_mem_Z H (Q.inv_mem (hV₁Q hc₁')) (Q.inv_mem (hV₂Q hc₂))))
    have hcC'' : c₂⁻¹ * c₁' * c₂ * c₂' ∈ CQt Q Z (Subgroup.zpowers y₀) :=
      (CQtGrp hc (Subgroup.zpowers y₀)).mul_mem hconj (mem_CQt_of_comm hy₀y₀ (hV₂Q hc₂') hz₂')
    rw [hy06] at hcC''
    have hcy : y₀ * (c₂⁻¹ * c₁' * c₂ * c₂') = (c₂⁻¹ * c₁' * c₂ * c₂') * y₀ := by
      have hle : (Q ⊓ Subgroup.centralizer ({y₀} : Set G)) ⊔ Z ≤
          Subgroup.centralizer ({y₀} : Set G) :=
        sup_le inf_le_right fun z hz =>
          Subgroup.mem_centralizer_iff.mpr fun t ht => by
            rw [Set.mem_singleton_iff.mp ht]; exact Sit.comm_of_mem_Z hsy0 hz
      exact Subgroup.mem_centralizer_iff.mp (hle hcC'') y₀ (Set.mem_singleton y₀)
    set c := c₁ * c₂ with hc_def
    set c'' := c₂⁻¹ * c₁' * c₂ * c₂' with hc''_def
    have hvcc : v = c * c'' := by
      rw [← hv12, e₁, e₂, hc_def, hc''_def]; group
    have hy' : y = c * y₀ * c⁻¹ := by
      have h1 : c'' * y₀ * c''⁻¹ = y₀ := by rw [← hcy]; group
      rw [hyv, hvcc, mul_inv_rev,
        show c * c'' * y₀ * (c''⁻¹ * c⁻¹) = c * (c'' * y₀ * c''⁻¹) * c⁻¹ by group, h1]
    have hx' : c⁻¹ * x * c = x := by
      rw [mul_assoc, hcx]; group
    have hxyc : c⁻¹ * (x * y) * c⁻¹⁻¹ = x * y₀ := by
      rw [hy', inv_inv]
      calc c⁻¹ * (x * (c * y₀ * c⁻¹)) * c = (c⁻¹ * x * c) * y₀ := by group
        _ = x * y₀ := by rw [hx']
    apply lin213_concl_conj c⁻¹
    rw [hxyc]
    have hty0 : IsTransvection (phiSL φ hr ⟨y₀, hy₀L⟩) := by
      have : phiSL φ hr ⟨y₀, hy₀L⟩ = phiSL φ hr ⟨y, hyL⟩ := by
        ext i j; simp [hφ0]
      rw [this]; exact hty
    exact lin213_of_compl H φ hr hker hQL hLM hLn hQn hCM hCQ hCQM hxC hy₀C hxL hy₀L hx htx hty0
      (by rw [hφ0]; exact hne)

end Assembly

theorem lin213OutsideStatement_of (h212 : Lin212Statement) :
    Lin213OutsideStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn x y hxM hyM hx hy hxQ hyQ hxyQ
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := lin31Statement_holds G M Q Z B n V₁ V₂ hb hc hS hn
  have h212' := h212 G M Q Z B n V₁' V₂' hb hc hS' hn
  obtain ⟨K, hK, hfin, hcard, φ, hr, hker, hZ₁, hV₁Q, hZ₂, hV₂Q, hI, hU, hs₁, hs₂, -, -⟩ := hS'
  have H := hc.hyp
  obtain ⟨m, -, hZm, -⟩ := H.cp
  haveI : CharP K 2 := charP_two_of_natCard_pow_two (hcard.trans hZm)
  obtain ⟨X, hsx⟩ := exists_sit H hx hxM hxQ
  obtain ⟨-, -, -, -, -, -, -, C, hCM, hCQ, hCQM, q, hq, hqC⟩ := h212' X x hsx
  have hqM : q ∈ M := cqt_Q_le_M H hq
  have hmemQ : ∀ {t : G}, t ∉ Q → q * t * q⁻¹ ∉ Q := fun {t} ht h => ht (by
    have := Q.mul_mem (Q.mul_mem (Q.inv_mem hq) h) hq
    rwa [show q⁻¹ * (q * t * q⁻¹) * q = t by group] at this)
  have hconjZ : ∀ {t : G}, InZClass Z t → InZClass Z (q * t * q⁻¹) := by
    rintro t ⟨a, z, hz, hz1, rfl⟩
    exact ⟨q * a, z, hz, hz1, by group⟩
  have hmul : q * x * q⁻¹ * (q * y * q⁻¹) = q * (x * y) * q⁻¹ := by group
  have h := lin213_core hc h212' hcard φ hr hker hZ₁ hV₁Q hZ₂ hV₂Q hI hU hs₁ hs₂ h31' hCM hCQ
    hCQM hqC (M.mul_mem (M.mul_mem hqM hxM) (M.inv_mem hqM))
    (M.mul_mem (M.mul_mem hqM hyM) (M.inv_mem hqM)) (hconjZ hx) (hconjZ hy) (hmemQ hxQ)
    (hmemQ hyQ) (by rw [hmul]; exact hmemQ hxyQ)
  rw [hmul] at h
  exact lin213_concl_conj q h

theorem lin213Statement_of (h212 : Lin212Statement) :
    Lin213Statement :=
  lin213Statement_of_outside
    (fun G _ _ M Q Z B V₁ V₂ hb hc hS => h212 G M Q Z B 2 V₁ V₂ hb hc hS le_rfl)
    (lin213OutsideStatement_of h212)

end CFSG.RankThree.GF2n.Smith81
