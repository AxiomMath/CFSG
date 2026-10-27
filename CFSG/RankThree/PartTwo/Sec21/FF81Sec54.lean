module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81S6Aut
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42B
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem mem_cenS_pair_iff {u v y : G} :
    y ∈ CenS (Subgroup.closure {u, v}) ↔ y * u = u * y ∧ y * v = v * y := by
  constructor
  · intro h
    exact ⟨(Subgroup.mem_centralizer_iff.mp h u (Subgroup.subset_closure (by simp))).symm,
      (Subgroup.mem_centralizer_iff.mp h v (Subgroup.subset_closure (by simp))).symm⟩
  · rintro ⟨hu, hv⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hle : Subgroup.closure ({u, v} : Set G) ≤ Cen y := (Subgroup.closure_le _).mpr (by
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hv.symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem mem_OUp_of_coprime {M : Subgroup G} {g : G} (hg : g ∈ M) (hc : Nat.Coprime 3 (orderOf g)) :
    g ∈ OUp 3 M := by
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subgroup.subset_normalClosure ?_, rfl⟩
  show Nat.Coprime 3 (orderOf (⟨g, hg⟩ : ↥M))
  rwa [Subgroup.orderOf_mk]

theorem OUp_le_of {M K : Subgroup G} (hKM : K ≤ M) (hn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (h3 : ∀ m ∈ M, Nat.Coprime 3 (orderOf m) → m ∈ K) : OUp 3 M ≤ K := by
  haveI : (K.subgroupOf M).Normal := ⟨fun k hk m => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hn m m.2 k hk⟩
  have hle : Subgroup.normalClosure {g : M | Nat.Coprime 3 (orderOf g)} ≤ K.subgroupOf M :=
    Subgroup.normalClosure_le_normal fun g hg => by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact h3 g g.2 (by rw [Subgroup.orderOf_coe]; exact hg)
  rintro _ ⟨g, hg, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (hle hg)

theorem FF81Basis.cen_dec' (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥) {y : G}
    (hy : y ∈ Cen b) : ∃ i : ℤ, ∃ l ∈ L, y = b ^ i * l := by
  obtain ⟨o, ho, i, l, hl, rfl⟩ := hB.cen_dec hy
  rw [h0, Subgroup.mem_bot] at ho
  exact ⟨i, l, hl, by rw [ho, one_mul]⟩

theorem FF81Sec5.ff81_5_4 (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    Nonempty (↥(OUp 3 (CenS (Subgroup.closure {b₂, b₃}))) ≃* Equiv.Perm (Fin 6)) ∧
      OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀ ∧
      b ∈ OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ∧
      b₁ ∈ OUp 3 (CenS (Subgroup.closure {b₂, b₃})) := by
  have hB := h5.basis
  have h0 := h5.opp_eq_bot
  set H := CenS (Subgroup.closure ({b₂, b₃} : Set G)) with hH
  have hset : ({b₂, b₁, b₃} : Set G) = {b₁, b₂, b₃} := Set.insert_comm _ _ _
  obtain ⟨⟨J', hJ'L, ⟨φ'⟩, hb₂J, hb₃J, hdecJ⟩, -⟩ := hKF G L hB.hyp.model b₂ b₁ b₃ hB.hb₂ hB.hb₁
    hB.hb₃ (by rw [hset]; exact hB.elem) (by rw [hset]; exact hB.selfcen) (by
      intro n hn hnN x hx
      rw [hset] at hnN
      have hx' : x ∈ ({b₁, b₂, b₃} : Set G) := hset ▸ hx
      have := hB.monoL_stab n hn hnN x hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
      tauto)
  obtain ⟨n, -, hn0, hn1, hn2, hn3⟩ := h5.mono4.1.2.2.2.2
  set α := n * n with hα
  have hαb : α * b * α⁻¹ = b₂ := by rw [hα, conj_conj, hn0, hn1]
  have hαb₁ : α * b₁ * α⁻¹ = b₃ := by rw [hα, conj_conj, hn1, hn2]
  have hαb₂ : α * b₂ * α⁻¹ = b := by rw [hα, conj_conj, hn2, hn3]
  have hαb₃ : α * b₃ * α⁻¹ = b₁ := by rw [hα, conj_conj, hn3, hn0]
  set K := conjBy α J' with hK
  have hmemK : ∀ j ∈ J', α * j * α⁻¹ ∈ K := fun j hj => ⟨j, hj, rfl⟩
  let ψ : ↥J' ≃* ↥K := J'.equivMapOfInjective (MulAut.conj α).toMonoidHom
    (MulAut.conj α).injective
  let φ : ↥K ≃* Equiv.Perm (Fin 6) := ψ.symm.trans φ'
  have hKH : K ≤ H := by
    rintro _ ⟨j, hj, rfl⟩
    have hjb : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC (hJ'L hj).1)
    have hjb₁ : j * b₁ = b₁ * j := Subgroup.mem_centralizer_singleton_iff.mp (hJ'L hj).2
    rw [mem_cenS_pair_iff]
    change α * j * α⁻¹ * b₂ = b₂ * (α * j * α⁻¹) ∧ α * j * α⁻¹ * b₃ = b₃ * (α * j * α⁻¹)
    rw [← hαb, ← hαb₁]
    constructor
    · calc α * j * α⁻¹ * (α * b * α⁻¹) = α * (j * b) * α⁻¹ := by group
        _ = α * (b * j) * α⁻¹ := by rw [hjb]
        _ = _ := by group
    · calc α * j * α⁻¹ * (α * b₁ * α⁻¹) = α * (j * b₁) * α⁻¹ := by group
        _ = α * (b₁ * j) * α⁻¹ := by rw [hjb₁]
        _ = _ := by group
  have hKc : ∀ k ∈ K, k * b₂ = b₂ * k ∧ k * b₃ = b₃ * k := fun k hk =>
    mem_cenS_pair_iff.mp (hKH hk)
  have hdec : ∀ y ∈ H, ∃ i : ℤ, ∃ k : ℕ, ∃ κ ∈ K, y = b₂ ^ i * b₃ ^ k * κ := by
    intro y hy
    obtain ⟨hy2, hy3⟩ := mem_cenS_pair_iff.mp hy
    set y' := α⁻¹ * y * α with hy'
    have hy'b : y' ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : b = α⁻¹ * b₂ * α := by rw [← hαb]; group
      rw [this, hy']
      calc α⁻¹ * y * α * (α⁻¹ * b₂ * α) = α⁻¹ * (y * b₂) * α := by group
        _ = α⁻¹ * (b₂ * y) * α := by rw [hy2]
        _ = _ := by group
    have hy'b₁ : y' * b₁ = b₁ * y' := by
      have : b₁ = α⁻¹ * b₃ * α := by rw [← hαb₁]; group
      rw [this, hy']
      calc α⁻¹ * y * α * (α⁻¹ * b₃ * α) = α⁻¹ * (y * b₃) * α := by group
        _ = α⁻¹ * (b₃ * y) * α := by rw [hy3]
        _ = _ := by group
    obtain ⟨i, l, hl, hyl⟩ := hB.cen_dec' h0 hy'b
    have hlb₁ : l ∈ L ⊓ Cen b₁ := by
      refine ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : Commute b₁ (b ^ i) := (Commute.zpow_left (hB.b_comm hB.hb₁) i).symm
      have hl' : l = (b ^ i)⁻¹ * y' := by rw [hyl]; group
      rw [hl']
      exact (h1.inv_right.mul_right (Commute.symm hy'b₁)).eq.symm
    obtain ⟨k, j, hj, hlj⟩ := hdecJ l hlb₁
    refine ⟨i, k, α * j * α⁻¹, hmemK j hj, ?_⟩
    calc y = α * y' * α⁻¹ := by rw [hy']; group
      _ = α * (b ^ i * (b₁ ^ k * j)) * α⁻¹ := by rw [hyl, hlj]
      _ = (α * b * α⁻¹) ^ i * (α * b₁ * α⁻¹) ^ k * (α * j * α⁻¹) := by
          rw [conj_zpow, conj_pow]; group
      _ = b₂ ^ i * b₃ ^ k * (α * j * α⁻¹) := by rw [hαb, hαb₁]
  obtain ⟨-, hb₂3, hb₃3, -, -, hb23⟩ := hB.b_facts
  have hβc : ∀ (i : ℤ) (k : ℕ), ∀ κ ∈ K, Commute (b₂ ^ i * b₃ ^ k) κ := fun i k κ hκ =>
    (Commute.zpow_left (hKc κ hκ).1.symm i).mul_left (Commute.pow_left (hKc κ hκ).2.symm k)
  have hβ3 : ∀ (i : ℤ) (k : ℕ), (b₂ ^ i * b₃ ^ k) ^ 3 = 1 := fun i k => by
    rw [((Commute.zpow_left hb23 i).pow_right k).mul_pow, ← zpow_natCast (b₂ ^ i), ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hb₂3, one_zpow, one_mul, ← pow_mul, mul_comm, pow_mul,
      hb₃3, one_pow]
  have h3K : ∀ y ∈ H, Nat.Coprime 3 (orderOf y) → y ∈ K := by
    intro y hy hc
    obtain ⟨i, k, κ, hκ, rfl⟩ := hdec y hy
    have hm := pow_orderOf_eq_one (b₂ ^ i * b₃ ^ k * κ)
    rw [(hβc i k κ hκ).mul_pow] at hm
    have hβm : (b₂ ^ i * b₃ ^ k) ^ orderOf (b₂ ^ i * b₃ ^ k * κ) ∈ K := by
      rw [eq_inv_of_mul_eq_one_left hm]; exact K.inv_mem (K.pow_mem hκ _)
    have hβm1 := eq_one_of_central φ hβm fun j hj => ((hβc i k j hj).pow_left _).eq
    have hβ1 : b₂ ^ i * b₃ ^ k = 1 := eq_one_of_dvd_three_pow (k := 1)
      (by rw [pow_one]; exact hβ3 i k) (orderOf_dvd_of_pow_eq_one hβm1) hc.symm
    rw [hβ1, one_mul]; exact hκ
  have hKn : ∀ m ∈ H, ∀ κ ∈ K, m * κ * m⁻¹ ∈ K := by
    intro m hm κ hκ
    obtain ⟨i, k, κ₀, hκ₀, rfl⟩ := hdec m hm
    have hκ' : κ₀ * κ * κ₀⁻¹ ∈ K := K.mul_mem (K.mul_mem hκ₀ hκ) (K.inv_mem hκ₀)
    rw [show b₂ ^ i * b₃ ^ k * κ₀ * κ * (b₂ ^ i * b₃ ^ k * κ₀)⁻¹ =
      (b₂ ^ i * b₃ ^ k) * (κ₀ * κ * κ₀⁻¹) * (b₂ ^ i * b₃ ^ k)⁻¹ by group,
      (hβc i k _ hκ').eq, mul_inv_cancel_right]
    exact hκ'
  have hinv : ∀ j ∈ K, j * j = 1 → Nat.Coprime 3 (orderOf j) := fun j _ hjj =>
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hjj))
      (by norm_num)
  have hJK : OUp 3 H = K := by
    refine le_antisymm (OUp_le_of hKH hKn h3K) ?_
    refine (le_closure_of_involutions φ (S := (OUp 3 H : Set G)) fun j hj hjj => ?_).trans
      (le_of_eq (Subgroup.closure_eq _))
    exact mem_OUp_of_coprime (hKH hj) (hinv j hj hjj)
  rw [hJK]
  have hbK : b ∈ K := hαb₂ ▸ hmemK b₂ hb₂J
  have hb₁K : b₁ ∈ K := hαb₃ ▸ hmemK b₃ hb₃J
  refine ⟨⟨φ⟩, ?_, hbK, hb₁K⟩
  have hs₀u : (b₂ * b₃) * s₀ = s₀ * (b₂ * b₃) :=
    Subgroup.mem_centralizer_iff.mp h5.hs₀A _ (Subgroup.subset_closure (by simp))
  have hs₀v : s₀ * (b₂ * b₃ ^ 2) * s₀⁻¹ = (b₂ * b₃ ^ 2)⁻¹ := h5.hs₀b
  have e1 : (b₂ * b₃) * (b₂ * b₃ ^ 2) = b₂ ^ 2 := by
    rw [show (b₂ * b₃) * (b₂ * b₃ ^ 2) = b₂ * (b₃ * b₂) * b₃ ^ 2 by group, ← hb23,
      show b₂ * (b₂ * b₃) * b₃ ^ 2 = b₂ ^ 2 * b₃ ^ 3 by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc], hb₃3,
      mul_one]
  have e2 : b₂ ^ 2 * b₂ ^ 2 = b₂ := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, hb₂3, one_mul, pow_one]
  have hs0H : ∀ y ∈ H, s₀ * y * s₀⁻¹ ∈ H := by
    intro y hy
    obtain ⟨hy2, hy3⟩ := mem_cenS_pair_iff.mp hy
    have hyu : Commute y (b₂ * b₃) := Commute.mul_right hy2 hy3
    have hyv : Commute y (b₂ * b₃ ^ 2) := Commute.mul_right hy2 (Commute.pow_right hy3 2)
    have hzu : Commute (s₀ * y * s₀⁻¹) (b₂ * b₃) := by
      have h := hyu.map (MulAut.conj s₀)
      simp only [MulAut.conj_apply] at h
      rwa [← hs₀u, mul_inv_cancel_right] at h
    have hzv : Commute (s₀ * y * s₀⁻¹) (b₂ * b₃ ^ 2) := by
      have h := hyv.inv_right.map (MulAut.conj s₀)
      simp only [MulAut.conj_apply] at h
      rwa [conj_inv', hs₀v, inv_inv] at h
    have hz2 : Commute (s₀ * y * s₀⁻¹) b₂ := by
      rw [← e2, ← e1]; exact (hzu.mul_right hzv).mul_right (hzu.mul_right hzv)
    have hz3 : Commute (s₀ * y * s₀⁻¹) b₃ := by
      rw [show b₃ = b₂⁻¹ * (b₂ * b₃) by group]; exact hz2.inv_right.mul_right hzu
    exact mem_cenS_pair_iff.mpr ⟨hz2.eq, hz3.eq⟩
  have hs0K : ∀ κ ∈ K, s₀ * κ * s₀⁻¹ ∈ K := by
    have hle : K ≤ (K.comap (MulAut.conj s₀).toMonoidHom) := by
      refine (le_closure_of_involutions φ (S := {j | j ∈ K ∧ j * j = 1})
        fun j hj hjj => ⟨hj, hjj⟩).trans ((Subgroup.closure_le _).mpr ?_)
      rintro j ⟨hj, hjj⟩
      refine h3K _ (hs0H j (hKH hj)) ?_
      rw [show (MulAut.conj s₀).toMonoidHom j = MulAut.conj s₀ j from rfl, MulEquiv.orderOf_eq]
      exact hinv j hj hjj
    exact fun κ hκ => hle hκ
  have hs₀2 : s₀ * s₀ = 1 := by rw [← sq, ← h5.hs₀, pow_orderOf_eq_one]
  let c₀ : ↥K →* ↥K := MonoidHom.mk' (fun κ => ⟨s₀ * κ * s₀⁻¹, hs0K κ κ.2⟩)
    (fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group))
  have hc₀ : ∀ κ : ↥K, (c₀ κ : G) = s₀ * κ * s₀⁻¹ := fun _ => rfl
  let σ : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6) :=
    φ.toMonoidHom.comp (c₀.comp φ.symm.toMonoidHom)
  have hσv : ∀ z, σ z = φ (c₀ (φ.symm z)) := fun _ => rfl
  have hc₀c₀ : ∀ κ : ↥K, c₀ (c₀ κ) = κ := fun κ => Subtype.ext (by
    rw [hc₀, hc₀, show s₀ * (s₀ * (κ : G) * s₀⁻¹) * s₀⁻¹ = (s₀ * s₀) * κ * (s₀ * s₀)⁻¹ by group,
      hs₀2, one_mul, inv_one, mul_one])
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    rw [hσv, hσv, MulEquiv.symm_apply_apply, hc₀c₀, MulEquiv.apply_symm_apply]
  set E := Subgroup.closure ({b, b₁} : Set G) with hE
  have hEK : E ≤ K := (Subgroup.closure_le _).mpr (by rintro _ (rfl | rfl) <;> assumption)
  have hEs : ∀ e ∈ E, s₀ * e * s₀⁻¹ = e := fun e he => by
    have he' : e ∈ Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) :=
      Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp) he
    rw [← Subgroup.mem_centralizer_iff.mp h5.hs₀A e he', mul_inv_cancel_right]
  have hEcard : Nat.card E = 9 := by
    refine le_antisymm (card_closure_pair_le hB.hyp.b_cube hB.b_facts.1 (hB.b_comm hB.hb₁)) ?_
    refine nine_le_card hB.mono.1 (hB.mem_B (by simp)) (hB.mem_B (by simp)) hB.hyp.b_ne_one ?_
    intro hb₁b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hb₁b
    have : b₁ ∈ L ⊓ CenS L := ⟨hB.hb₁, Subgroup.mem_centralizer_iff.mpr fun l hl => by
      rw [← hi]; exact (Commute.zpow_left (hB.b_comm hl) i).eq.symm⟩
    rw [hB.inf_cenS_self, Subgroup.mem_bot] at this
    exact ne_one_of_basis hB.elem this
  set P := (E.subgroupOf K).map φ.toMonoidHom with hP
  have hPcard : Nat.card P = 9 := by
    rw [hP, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hEcard]
  have hfix : ∀ z ∈ P, σ z = z := by
    rintro _ ⟨κ, hκ, rfl⟩
    show σ (φ κ) = φ κ
    rw [hσv, MulEquiv.symm_apply_apply]
    congr 1
    exact Subtype.ext (by rw [hc₀]; exact hEs _ (Subgroup.mem_subgroupOf.mp hκ))
  intro κ hκ
  have h := S6Aut.eq_of_fix_sylow σ hσσ hPcard hfix (φ ⟨κ, hκ⟩)
  rw [hσv, MulEquiv.symm_apply_apply] at h
  have h' := congrArg Subtype.val (φ.injective h)
  rw [hc₀] at h'
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc κ * s₀ = (s₀ * κ * s₀⁻¹) * s₀ := by rw [h']
    _ = s₀ * κ := by group

end CFSG.RankThree.PartTwo.Sec21.FF81
