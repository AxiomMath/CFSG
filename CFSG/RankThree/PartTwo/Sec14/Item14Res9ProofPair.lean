module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Res9Pair

open Item148PtRes

theorem le_of_isPerfect_of_forall_pow_mem {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {P M : Subgroup G} (hP : Group.IsPerfect P)
    (hPM : P ≤ Subgroup.normalizer (M : Set G)) (hpow : ∀ x ∈ P, ∃ e : ℕ, x ^ (p ^ e) ∈ M) :
    P ≤ M := by
  set K : Subgroup ↥P := M.subgroupOf P with hK
  have hKn : K.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPM
  have hpg : IsPGroup p (↥P ⧸ K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    obtain ⟨e, he⟩ := hpow x x.2
    refine ⟨e, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf]
    simpa using he
  have := hP
  have hperf : Group.IsPerfect (↥P ⧸ K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective K)
  have hsub : Subsingleton (↥P ⧸ K) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥P ⧸ K) hpg.isNilpotent
  intro x hx
  have h1 : QuotientGroup.mk' K (⟨x, hx⟩ : ↥P) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf] at h1
  exact h1

section Pair

variable {Γ : Type*} [Group Γ] [Finite Γ]

structure IsPair (U V : Subgroup Γ) : Prop where
  normal_left : U.Normal
  normal_right : V.Normal
  sup_eq : U ⊔ V = ⊤
  comm_eq : ⁅U, V⁆ = ⊥
  card_inf : Nat.card ↥(U ⊓ V) = 3
  cover_left : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6))
  cover_right : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6))

omit [Finite Γ] in
theorem exists_isPair (h : IsCentralProductA6Covers Γ) : ∃ U V : Subgroup Γ, IsPair U V := by
  obtain ⟨U, V, hUn, hVn, hUV', hUV, h3, hTU, hTV⟩ := h
  exact ⟨U, V, ⟨hUn, hVn, hUV', hUV, h3, hTU, hTV⟩⟩

omit [Finite Γ] in
theorem IsPair.symm {U V : Subgroup Γ} (h : IsPair U V) : IsPair V U where
  normal_left := h.normal_right
  normal_right := h.normal_left
  sup_eq := by rw [sup_comm]; exact h.sup_eq
  comm_eq := by rw [Subgroup.commutator_comm]; exact h.comm_eq
  card_inf := by rw [inf_comm]; exact h.card_inf
  cover_left := h.cover_right
  cover_right := h.cover_left

@[expose] def TrivOn (σ : MulAut Γ) (U : Subgroup Γ) : Prop :=
  ∀ y ∈ U, σ y * y⁻¹ ∈ Item148PtRes.centerIn U

omit [Finite Γ] in
theorem TrivOn.mul {σ τ : MulAut Γ} {U : Subgroup Γ} (hσ : TrivOn σ U) (hτ : TrivOn τ U) :
    TrivOn (σ * τ) U := by
  intro y hy
  have hτy : τ y ∈ U := by
    have e : τ y = (τ y * y⁻¹) * y := by group
    rw [e]
    exact mul_mem (Item148PtRes.centerIn_le U (hτ y hy)) hy
  have e : (σ * τ) y * y⁻¹ = (σ (τ y) * (τ y)⁻¹) * (τ y * y⁻¹) := by
    rw [MulAut.mul_apply]
    group
  rw [e]
  exact mul_mem (hσ _ hτy) (hτ y hy)

theorem IsPair.centerIn_le_center {U V : Subgroup Γ} (hP : IsPair U V) :
    Item148PtRes.centerIn U ≤ Subgroup.center Γ := by
  have := hP.normal_left
  have hUZ := inf_eq_centerIn_left hP.comm_eq hP.card_inf hP.cover_left.1
  intro x hx
  exact mem_center_of_mem_inf hP.sup_eq hP.comm_eq (hUZ ▸ hx)

theorem IsPair.inf_eq {U V : Subgroup Γ} (hP : IsPair U V) : U ⊓ V = Item148PtRes.centerIn U :=
  inf_eq_centerIn_left hP.comm_eq hP.card_inf hP.cover_left.1

theorem IsPair.centerIn_eq {U V : Subgroup Γ} (hP : IsPair U V) :
    Item148PtRes.centerIn U = Item148PtRes.centerIn V := by
  rw [← hP.inf_eq, inf_comm, hP.symm.inf_eq]

theorem IsPair.mem_right_of_fixed [Group.IsPerfect Γ] {U V : Subgroup Γ} (hP : IsPair U V)
    {σ : MulAut Γ} (hσ3 : σ ^ 3 = 1) (hσ : ¬ TrivOn σ U) {z : Γ} (hz : σ z = z) {k : ℕ}
    (hzk : z ^ k = 1) (hk3 : Nat.Coprime k 3) : z ∈ V := by
  have := hP.normal_left
  have := hP.normal_right
  obtain ⟨hσU, hσV⟩ := map_eq_of_pow_three hP.sup_eq hP.comm_eq hP.card_inf hP.cover_left
    hP.cover_right hσ3
  obtain ⟨-, ⟨eU⟩⟩ := hP.cover_left
  have hUZ := hP.inf_eq
  unfold TrivOn at hσ
  push Not at hσ
  obtain ⟨y₀, hy₀, hy₀σ⟩ := hσ
  obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_eq hP.sup_eq z
  obtain ⟨h1, -, h3', -⟩ := fixed_components hP.sup_eq hP.comm_eq hσU hσV hy hv hz hzk
  have hyZ := mem_centerIn_of_fixed eU hσ3 hσU hy₀ hy₀σ hy (hUZ ▸ h1) (hUZ ▸ h3') hk3
  rw [← hUZ] at hyZ
  exact mul_mem hyZ.2 hv

theorem IsPair.exists_pow_mem_right_of_fixed [Group.IsPerfect Γ] {U V : Subgroup Γ}
    (hP : IsPair U V) {σ : MulAut Γ} (hσ3 : σ ^ 3 = 1) (hσ : ¬ TrivOn σ U) {z : Γ}
    (hz : σ z = z) : ∃ e : ℕ, z ^ (3 ^ e) ∈ V := by
  obtain ⟨e, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 3 (by norm_num)
  refine ⟨e, hP.mem_right_of_fixed hσ3 hσ (by rw [map_pow, hz]) (k := m) ?_ ?_⟩
  · rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm

theorem IsPair.eq_of_trivOn [Group.IsPerfect Γ] {U V : Subgroup Γ} (hP : IsPair U V)
    {σ : MulAut Γ} (hU : TrivOn σ U) (hV : TrivOn σ V) (g : Γ) : σ g = g := by
  have := hP.normal_left
  have := hP.normal_right
  have htop := top_eq_commutator_sup hP.sup_eq hP.comm_eq
  have hg : g ∈ ⁅U, U⁆ ⊔ ⁅V, V⁆ := htop ▸ Subgroup.mem_top g
  have hle : ⁅U, U⁆ ⊔ ⁅V, V⁆ ≤ MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id _) :=
    sup_le (fun x hx => fixed_of_mem_commutator hP.centerIn_le_center hU hx)
      (fun x hx => fixed_of_mem_commutator hP.symm.centerIn_le_center hV hx)
  exact hle hg

omit [Finite Γ] in
theorem IsPair.mem_commutator_left [Group.IsPerfect Γ] {U V : Subgroup Γ} (hP : IsPair U V)
    {z : Γ} (hzU : z ∈ U) {k : ℕ} (hzk : z ^ k = 1) (hk3 : Nat.Coprime k 3) : z ∈ ⁅U, U⁆ := by
  have := hP.normal_left
  have := hP.normal_right
  exact mem_commutator_of_mem (U := V) (V := U) hP.symm.sup_eq hP.symm.comm_eq hP.symm.card_inf
    hzU hzk hk3

theorem IsPair.commutator_le_of_le_left {U V Λ : Subgroup Γ} (hP : IsPair U V) (hΛU : Λ ≤ U)
    (hΓ : ∀ g : Γ, ∃ v ∈ V, ∃ l ∈ Λ, g = v * l) : ⁅U, U⁆ ≤ Λ := by
  have hdec : ∀ u ∈ U, ∃ l ∈ Λ, ∃ z ∈ Subgroup.center Γ, u = l * z := by
    intro u hu
    obtain ⟨v, hv, l, hl, rfl⟩ := hΓ u
    have hvU : v ∈ U := by
      have e : v = v * l * l⁻¹ := by group
      rw [e]
      exact mul_mem hu (inv_mem (hΛU hl))
    have hvc : v ∈ Subgroup.center Γ := hP.centerIn_le_center (hP.inf_eq ▸ ⟨hvU, hv⟩)
    refine ⟨l, hl, v, hvc, ?_⟩
    exact (Subgroup.mem_center_iff.mp hvc l).symm
  rw [Subgroup.commutator_le]
  intro u₁ hu₁ u₂ hu₂
  obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := hdec u₁ hu₁
  obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := hdec u₂ hu₂
  rw [Item148HJ.commutatorElement_mul_central hz₁ hz₂]
  exact Subgroup.commutator_mem_commutator hl₁ hl₂ |> fun h => Subgroup.commutator_le_self Λ h

theorem IsPair.commutator_le_of_trivOn_right [Group.IsPerfect Γ] {U V Λ : Subgroup Γ}
    (hP : IsPair U V) (hΓ : ∀ g : Γ, ∃ v ∈ V, ∃ l ∈ Λ, g = v * l) {σ : MulAut Γ}
    (hσ3 : σ ^ 3 = 1) (hσΛ : ∀ l ∈ Λ, σ l ∈ Λ) (hσV : TrivOn σ V) (hσU : ¬ TrivOn σ U) :
    ⁅U, U⁆ ≤ Λ := by
  have := hP.normal_left
  have := hP.normal_right
  obtain ⟨hσUU, -⟩ := map_eq_of_pow_three hP.sup_eq hP.comm_eq hP.card_inf hP.cover_left
    hP.cover_right hσ3
  obtain ⟨-, ⟨eU⟩⟩ := hP.cover_left
  have hcen := hP.centerIn_le_center
  have hZUV : Item148PtRes.centerIn V = Item148PtRes.centerIn U := hP.centerIn_eq.symm
  set W : Subgroup Γ := Λ ⊓ U with hW
  have hconj : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
    intro u hu w hw
    obtain ⟨v, hv, l, hl, rfl⟩ := hΓ u
    have hlw : l * w * l⁻¹ ∈ U := hP.normal_left.conj_mem w (Subgroup.mem_inf.mp hw).2 l
    have hvc : v * (l * w * l⁻¹) = (l * w * l⁻¹) * v :=
      (commute_of_commutator_eq_bot hP.comm_eq hlw hv).symm
    have e : v * l * w * (v * l)⁻¹ = l * w * l⁻¹ := by
      calc v * l * w * (v * l)⁻¹ = v * (l * w * l⁻¹) * v⁻¹ := by group
        _ = l * w * l⁻¹ := by rw [hvc]; group
    rw [e]
    have hw' := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hl hw'.1) (inv_mem hl), hlw⟩
  have hUW : U ≤ Subgroup.normalizer (W : Set Γ) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hconj u hu w
    · intro h
      have := hconj u⁻¹ (inv_mem hu) _ h
      simpa [mul_assoc] using this
  have hWZ : ¬ W ≤ Item148PtRes.centerIn U := by
    intro hle
    apply hσU
    intro u₀ hu₀
    obtain ⟨v, hv, l, hl, rfl⟩ := hΓ u₀
    set c := σ v * v⁻¹ with hc
    have hcZ : c ∈ Item148PtRes.centerIn U := hZUV ▸ hσV v hv
    have hcc : c ∈ Subgroup.center Γ := hcen hcZ
    have hσu : σ (v * l) ∈ U := hσUU ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hu₀
    have hd : σ (v * l) * (v * l)⁻¹ ∈ U := mul_mem hσu (inv_mem hu₀)
    have hvd : v * (σ (v * l) * (v * l)⁻¹) = (σ (v * l) * (v * l)⁻¹) * v :=
      (commute_of_commutator_eq_bot hP.comm_eq hd hv).symm
    have hσv : σ v = c * v := by rw [hc]; group
    set d := σ (v * l) * (v * l)⁻¹ with hd'
    have e : σ l * l⁻¹ = d * c⁻¹ := by
      have h1 : σ l = (σ v)⁻¹ * σ (v * l) := by rw [map_mul]; group
      have h2 : σ l * l⁻¹ = v⁻¹ * c⁻¹ * d * v := by
        rw [h1, hσv, hd']
        group
      have hvd' : v⁻¹ * d * v = d := by
        rw [mul_assoc, ← hvd]
        group
      have hcv : v⁻¹ * c⁻¹ = c⁻¹ * v⁻¹ := Subgroup.mem_center_iff.mp (inv_mem hcc) v⁻¹
      calc σ l * l⁻¹ = v⁻¹ * c⁻¹ * d * v := h2
        _ = c⁻¹ * (v⁻¹ * d * v) := by rw [hcv]; group
        _ = c⁻¹ * d := by rw [hvd']
        _ = d * c⁻¹ := (Subgroup.mem_center_iff.mp (inv_mem hcc) d).symm
    have hmem : σ l * l⁻¹ ∈ W := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (hσΛ l hl) (inv_mem hl), ?_⟩
      rw [e]
      exact mul_mem hd (inv_mem (Item148PtRes.centerIn_le U hcZ))
    have h4 := hle hmem
    rw [e] at h4
    have h5 : d = (d * c⁻¹) * c := by group
    rw [h5]
    exact mul_mem h4 hcZ
  rcases inf_le_centerIn_or eU hUW with h1 | h1
  · exact absurd (by rwa [show W ⊓ U = W from inf_eq_left.mpr inf_le_right] at h1) hWZ
  · have hdec : ∀ u ∈ U, ∃ w ∈ Λ, ∃ z ∈ Subgroup.center Γ, u = w * z := by
      intro u hu
      obtain ⟨w, hw, hwz⟩ := h1 u hu
      exact ⟨w, (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hw).1).1, w⁻¹ * u, hcen hwz,
        by group⟩
    rw [Subgroup.commutator_le]
    intro u₁ hu₁ u₂ hu₂
    obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := hdec u₁ hu₁
    obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := hdec u₂ hu₂
    rw [Item148HJ.commutatorElement_mul_central hz₁ hz₂]
    exact Subgroup.commutator_le_self Λ (Subgroup.commutator_mem_commutator hl₁ hl₂)

omit [Finite Γ] in
theorem IsPair.eq_one_of_mem_inf {U V : Subgroup Γ} (hP : IsPair U V) {z : Γ} (hz : z ∈ U ⊓ V)
    {k : ℕ} (hzk : z ^ k = 1) (hk3 : Nat.Coprime k 3) : z = 1 := by
  have h1 := Subgroup.orderOf_dvd_natCard (U ⊓ V) hz
  rw [hP.card_inf] at h1
  have hd : orderOf z ∣ Nat.gcd k 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzk) h1
  rw [hk3, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

theorem IsPair.eq_one_of_fixed_both [Group.IsPerfect Γ] {U V : Subgroup Γ} (hP : IsPair U V)
    {σ₁ σ₂ : MulAut Γ} (h₁3 : σ₁ ^ 3 = 1) (h₂3 : σ₂ ^ 3 = 1) (h₁ : ¬ TrivOn σ₁ U)
    (h₂ : ¬ TrivOn σ₂ V) {z : Γ} (hz₁ : σ₁ z = z) (hz₂ : σ₂ z = z) {k : ℕ} (hzk : z ^ k = 1)
    (hk3 : Nat.Coprime k 3) : z = 1 :=
  hP.eq_one_of_mem_inf (Subgroup.mem_inf.mpr ⟨hP.symm.mem_right_of_fixed h₂3 h₂ hz₂ hzk hk3,
    hP.mem_right_of_fixed h₁3 h₁ hz₁ hzk hk3⟩) hzk hk3

theorem IsPair.mul_inv_mem_left_of_trivOn_right [Group.IsPerfect Γ] {U V : Subgroup Γ}
    (hP : IsPair U V) {σ : MulAut Γ} (hσ3 : σ ^ 3 = 1) (hσV : TrivOn σ V) (γ : Γ) :
    γ * (σ γ)⁻¹ ∈ U := by
  have := hP.normal_left
  have := hP.normal_right
  obtain ⟨hσU, -⟩ := map_eq_of_pow_three hP.sup_eq hP.comm_eq hP.card_inf hP.cover_left
    hP.cover_right hσ3
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_eq hP.sup_eq γ
  have hσu : σ u ∈ U := hσU ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hu
  have hc : σ v * v⁻¹ ∈ U := by
    have h1 := hσV v hv
    rw [← hP.centerIn_eq, ← hP.inf_eq] at h1
    exact (Subgroup.mem_inf.mp h1).1
  have e : u * v * (σ (u * v))⁻¹ = u * (σ v * v⁻¹)⁻¹ * (σ u)⁻¹ := by
    rw [map_mul]
    group
  rw [e]
  exact mul_mem (mul_mem hu (inv_mem hc)) (inv_mem hσu)

end Pair

end Res9Pair

end CFSG.RankThree.PartTwo.Sec14
