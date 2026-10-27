module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79JT
public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Sylow
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Dec
public import Certificates.Data.ExceptionalSL3

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

structure Ctl (b x : H) (Q : Subgroup H) : Prop where
  le_nor : Q ≤ Nor (Subgroup.zpowers x)
  norm : ∀ g ∈ Nor (Subgroup.zpowers x), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q
  cop : Nat.Coprime 3 (Nat.card Q)
  decomp : ∀ g ∈ Nor (Subgroup.zpowers x), ∃ q ∈ Q,
    ∃ n ∈ Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers x), g = q * n

theorem Ctl.of_N_bi {b x : H}
    (h : setMul (Opp 3 (Nor (Subgroup.zpowers x)))
      (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers x)) = Nor (Subgroup.zpowers x)) :
    Ctl b x (Opp 3 (Nor (Subgroup.zpowers x))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨L14.Opp_le 3 _, fun g hg q hq => L14.Opp_conj_mem hg hq, L14.Opp_coprime 3 _, ?_⟩
  intro g hg
  have hmem : g ∈ setMul (Opp 3 (Nor (Subgroup.zpowers x)))
      (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers x)) := by
    rw [h]
    exact hg
  obtain ⟨q, hq, n, hn, hgqn⟩ := hmem
  exact ⟨q, hq, n, hn, hgqn⟩

theorem fs79_cen_le_nor_zpowers (x : H) : Cen x ≤ Nor (Subgroup.zpowers x) := by
  intro g hg
  refine Subgroup.centralizer_le_normalizer _ ?_
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg : Commute g x) k).eq.symm

theorem eq_one_of_mem_coprime_of_pow_three {S : Subgroup H} (hS : Nat.Coprime 3 (Nat.card S))
    {x : H} (hx : x ∈ S) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥S) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have h2 : orderOf (⟨x, hx⟩ : ↥S) ∣ Nat.card S := orderOf_dvd_natCard _
  have h3' := Nat.eq_one_of_dvd_coprimes hS h1 h2
  have := orderOf_eq_one_iff.1 h3'
  simpa using congrArg Subtype.val this

theorem closure_bb₁b₂_eq (b b₁ b₂ : H) :
    Subgroup.closure ({b, b₁, b₂} : Set H) =
      Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂} : Set H) := by
  rw [Subgroup.zpowers_eq_closure b, ← Subgroup.closure_union]
  congr 1


theorem FS79Hyp.B_comm (h : FS79Hyp b t b₁ b₂ J) {u v : H}
    (hu : u ∈ Subgroup.closure ({b, b₁, b₂} : Set H))
    (hv : v ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) : u * v = v * u := by
  have hE := h.isElemAb_B
  exact congrArg Subtype.val (hE.1.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem FS79Hyp.B_pow_three (h : FS79Hyp b t b₁ b₂ J) {u : H}
    (hu : u ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) : u ^ 3 = 1 := by
  have hE := h.isElemAb_B
  haveI := hE.1
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) u hu

theorem eq_or_inv_of_mem_zpowers_of_pow_three {x z : H} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hz : z ∈ Subgroup.zpowers x) (hz1 : z ≠ 1) : z = x ∨ z = x⁻¹ := by
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← zpow_mod_orderOf, hord] at hz1 ⊢
  have hk : (k % ((3 : ℕ) : ℤ)) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h0 | h0 | h0 <;> rw [h0] at hz1 ⊢
  · exact absurd (zpow_zero x) hz1
  · left
    exact zpow_one x
  · right
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx3])

theorem FS79Hyp.mem_zpowers_of_comm (h : FS79Hyp b t b₁ b₂ J) {y : H}
    (hy : y ∈ Subgroup.closure ({b, t} : Set H)) (hc : y * b = b * y) :
    y ∈ Subgroup.zpowers b := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.ord_t]
    exact pow_orderOf_eq_one t
  obtain ⟨i, hi | hi⟩ := mem_closure_bt_iff h.inv_b ht2 hy
  · rw [hi]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i
  · exfalso
    rw [hi] at hc
    have h1 : t * b = b * t := by
      have : b ^ i * (t * b) = b ^ i * (b * t) := by
        calc b ^ i * (t * b) = b ^ i * t * b := by group
          _ = b * (b ^ i * t) := hc
          _ = b ^ i * (b * t) := by
            rw [← mul_assoc, ← mul_assoc, (Commute.zpow_left (Commute.refl b) i).eq]
      exact mul_left_cancel this
    have h2 : b = b⁻¹ := by
      rw [← h.inv_b]
      calc b = (t * b) * t⁻¹ := by rw [h1]; group
        _ = t * b * t⁻¹ := rfl
    have hb2 : b ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp h2
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2
    rw [h.ord_b] at hdvd
    norm_num at hdvd


theorem FS79Hyp.B₁_le_J (h : FS79Hyp b t b₁ b₂ J) :
    Subgroup.closure ({b₁, b₂} : Set H) ≤ J := by
  rw [Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | rfl
  · exact h.b₁_mem
  · exact h.b₂_mem

theorem FS79Hyp.B₁_le_B (b b₁ b₂ : H) :
    Subgroup.closure ({b₁, b₂} : Set H) ≤ Subgroup.closure ({b, b₁, b₂} : Set H) := by
  rw [closure_bb₁b₂_eq]
  exact le_sup_right

theorem FS79Hyp.zpowers_le_B (b b₁ b₂ : H) :
    Subgroup.zpowers b ≤ Subgroup.closure ({b, b₁, b₂} : Set H) := by
  rw [closure_bb₁b₂_eq]
  exact le_sup_left

theorem Ctl.eq_one_of_mem_M0 (h : FS79Hyp b t b₁ b₂ J) {x : H} {Q : Subgroup H}
    (hQ : Ctl b x Q) (hxB : x ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hx1 : x ≠ 1) {w : H}
    (hwM : w ∈ Subgroup.closure ({b, t} : Set H) ⊔ J)
    (hwS : w ∈ Opp 3 (Nor (Subgroup.zpowers b)) ⊔ Q) : w = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup H := Opp 3 (Nor (Subgroup.zpowers b)) with hK
  set B₁ : Subgroup H := Subgroup.closure ({b₁, b₂} : Set H) with hB₁
  set B : Subgroup H := Subgroup.closure ({b, b₁, b₂} : Set H) with hB
  have hB₁J : B₁ ≤ J := h.B₁_le_J
  have hB₁B : B₁ ≤ B := FS79Hyp.B₁_le_B b b₁ b₂
  have hbB : b ∈ B := FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b)
  have hxJ : x ∈ J := hB₁J hxB
  have hxBB : x ∈ B := hB₁B hxB
  have hKx : K ≤ Nor (Subgroup.zpowers x) := fun κ hκ =>
    fs79_cen_le_nor_zpowers x (Subgroup.mem_centralizer_singleton_iff.mpr (h.K_comm_J hκ hxJ))
  have hSx : K ⊔ Q ≤ Nor (Subgroup.zpowers x) := sup_le hKx hQ.le_nor
  have hKnorm : K ≤ Subgroup.normalizer (Q : Set H) := by
    intro κ hκ
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hQ.norm κ (hKx hκ) q hq
    · intro hq
      have := hQ.norm κ⁻¹ ((Nor (Subgroup.zpowers x)).inv_mem (hKx hκ)) _ hq
      simpa [mul_assoc] using this
  have hScop : Nat.Coprime 3 (Nat.card ↥(K ⊔ Q)) := by
    have hmul :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hKnorm
    have hKQ : Nat.Coprime 3 (Nat.card K * Nat.card Q) :=
      Nat.Coprime.mul_right (L14.Opp_coprime 3 _) hQ.cop
    exact hKQ.coprime_dvd_right (Dvd.intro _ hmul)
  have hBnorN : ∀ β ∈ B, β ∈ Nor (Subgroup.zpowers b) := fun β hβ =>
    fs79_cen_le_nor_zpowers b (Subgroup.mem_centralizer_singleton_iff.mpr (h.B_comm hβ hbB))
  have hBnorX : ∀ β ∈ B, β ∈ Nor (Subgroup.zpowers x) := fun β hβ =>
    fs79_cen_le_nor_zpowers x (Subgroup.mem_centralizer_singleton_iff.mpr (h.B_comm hβ hxBB))
  have hBS : ∀ β ∈ B, ∀ s ∈ K ⊔ Q, β * s * β⁻¹ ∈ K ⊔ Q := by
    intro β hβ s hs
    rw [Subgroup.sup_eq_closure] at hs
    refine Subgroup.closure_induction (p := fun s _ => β * s * β⁻¹ ∈ K ⊔ Q) ?_ ?_ ?_ ?_ hs
    · intro z hz
      rcases hz with hz | hz
      · exact Subgroup.mem_sup_left (L14.Opp_conj_mem (hBnorN β hβ) hz)
      · exact Subgroup.mem_sup_right (hQ.norm β (hBnorX β hβ) z hz)
    · simp
    · intro a c _ _ ha hc
      have : β * (a * c) * β⁻¹ = (β * a * β⁻¹) * (β * c * β⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hc
    · intro a _ ha
      have : β * a⁻¹ * β⁻¹ = (β * a * β⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  obtain ⟨y, hy, j, hj, rfl⟩ := (CFSG.mem_sup_of_commute
    (A := Subgroup.closure ({b, t} : Set H)) (B := J)
    (fun a ha c hc => h.Y_comm_J ha hc)).mp hwM
  have hyN : y ∈ Nor (Subgroup.zpowers b) := h.Y_le_Nor hy
  have hjx : j * x * j⁻¹ ∈ Subgroup.zpowers x := by
    have hwx := hSx hwS
    have h1 := (Subgroup.mem_normalizer_iff.mp hwx x).mp (Subgroup.mem_zpowers x)
    have hjxJ : j * x * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hxJ) (J.inv_mem hj)
    have hyc : y * (j * x * j⁻¹) = (j * x * j⁻¹) * y := h.Y_comm_J hy hjxJ
    have e : y * j * x * (y * j)⁻¹ = j * x * j⁻¹ := by
      calc y * j * x * (y * j)⁻¹ = y * (j * x * j⁻¹) * y⁻¹ := by group
        _ = (j * x * j⁻¹) * y * y⁻¹ := by rw [hyc]
        _ = j * x * j⁻¹ := by group
    rwa [e] at h1
  have hjx1 : j * x * j⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    calc x = j⁻¹ * (j * x * j⁻¹) * j := by group
      _ = 1 := by rw [h1]; group
  have hjx' : j * x * j⁻¹ = x ∨ j * x * j⁻¹ = x⁻¹ :=
    eq_or_inv_of_mem_zpowers_of_pow_three (h.B_pow_three hxBB) hx1 hjx hjx1
  have hjB₁ := h.normalizes_B₁_of_conj_line hxB hx1 hj hjx'
  have hbcomm : ∀ a ∈ Subgroup.zpowers b, ∀ c ∈ B₁, Commute a c := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
      (h.J_le_cen_b (hB₁J hc)) : Commute c b) k).symm
  have hwB : ∀ β ∈ B, y * j * β * (y * j)⁻¹ ∈ B := by
    intro β hβ
    have hβ' : β ∈ Subgroup.zpowers b ⊔ B₁ := by rwa [hB, closure_bb₁b₂_eq] at hβ
    obtain ⟨u, hu, z, hz, rfl⟩ := (CFSG.mem_sup_of_commute hbcomm).mp hβ'
    have hzJ : z ∈ J := hB₁J hz
    have hjzJ : j * z * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hzJ) (J.inv_mem hj)
    have hju : j * u = u * j := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
        (h.J_le_cen_b hj) : Commute j b) k).eq
    have hyz : y * (j * z * j⁻¹) = (j * z * j⁻¹) * y := h.Y_comm_J hy hjzJ
    have e : y * j * (u * z) * (y * j)⁻¹ = (y * u * y⁻¹) * (j * z * j⁻¹) := by
      calc y * j * (u * z) * (y * j)⁻¹ = y * (j * u) * z * j⁻¹ * y⁻¹ := by group
        _ = y * (u * j) * z * j⁻¹ * y⁻¹ := by rw [hju]
        _ = y * u * (j * z * j⁻¹) * y⁻¹ := by group
        _ = y * u * ((j * z * j⁻¹) * y⁻¹ * y) * y⁻¹ := by group
        _ = y * u * (y⁻¹ * (y * (j * z * j⁻¹)) ) * y⁻¹ := by group
        _ = y * u * (y⁻¹ * ((j * z * j⁻¹) * y)) * y⁻¹ := by rw [hyz]
        _ = (y * u * y⁻¹) * (j * z * j⁻¹) := by group
    rw [e, hB, closure_bb₁b₂_eq]
    refine Subgroup.mul_mem_sup ?_ (hjB₁ z hz)
    have := (Subgroup.mem_normalizer_iff.mp hyN u).mp hu
    exact this
  have hcomm : ∀ β ∈ B, β * (y * j) * β⁻¹ * (y * j)⁻¹ = 1 := by
    intro β hβ
    have h1 : β * (y * j) * β⁻¹ ∈ K ⊔ Q := hBS β hβ _ hwS
    have h2 : β * (y * j) * β⁻¹ * (y * j)⁻¹ ∈ K ⊔ Q :=
      (K ⊔ Q).mul_mem h1 ((K ⊔ Q).inv_mem hwS)
    have h3 : β * (y * j) * β⁻¹ * (y * j)⁻¹ ∈ B := by
      have : β * (y * j) * β⁻¹ * (y * j)⁻¹ = β * ((y * j) * β⁻¹ * (y * j)⁻¹) := by group
      rw [this]
      exact B.mul_mem hβ (hwB β⁻¹ (B.inv_mem hβ))
    exact eq_one_of_mem_coprime_of_pow_three hScop h2 (h.B_pow_three h3)
  have hcomm' : ∀ β ∈ B, β * (y * j) = (y * j) * β := by
    intro β hβ
    have := hcomm β hβ
    calc β * (y * j) = (β * (y * j) * β⁻¹ * (y * j)⁻¹) * ((y * j) * β) := by group
      _ = (y * j) * β := by rw [this, one_mul]
  have hjb : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj)
  have hyb : y * b = b * y := by
    have := hcomm' b hbB
    have e : b * y * j = y * b * j := by
      calc b * y * j = b * (y * j) := by group
        _ = (y * j) * b := this
        _ = y * (j * b) := by group
        _ = y * (b * j) := by rw [hjb]
        _ = y * b * j := by group
    exact (mul_right_cancel e).symm
  have hyz : y ∈ Subgroup.zpowers b := h.mem_zpowers_of_comm hy hyb
  have hjc : ∀ z ∈ B₁, j * z = z * j := by
    intro z hz
    have hzB : z ∈ B := hB₁B hz
    have hzJ : z ∈ J := hB₁J hz
    have h1 : z * (y * j) = (y * j) * z := hcomm' z hzB
    have hyzc : y * z = z * y := h.Y_comm_J hy hzJ
    have h2 : y * (z * j) = y * (j * z) := by
      calc y * (z * j) = (y * z) * j := by group
        _ = (z * y) * j := by rw [hyzc]
        _ = z * (y * j) := by group
        _ = (y * j) * z := h1
        _ = y * (j * z) := by group
    exact (mul_left_cancel h2).symm
  have hb₁B₁ : b₁ ∈ B₁ := Subgroup.subset_closure (by simp)
  have hb₂B₁ : b₂ ∈ B₁ := Subgroup.subset_closure (by simp)
  have hjB₁' : j ∈ B₁ := h.mem_B₁_of_cen hj (hjc b₁ hb₁B₁) (hjc b₂ hb₂B₁)
  have hwB' : y * j ∈ B :=
    B.mul_mem (FS79Hyp.zpowers_le_B b b₁ b₂ hyz) (hB₁B hjB₁')
  exact eq_one_of_mem_coprime_of_pow_three hScop hwS (h.B_pow_three hwB')


theorem Ctl.conj_in_M0 (h : FS79Hyp b t b₁ b₂ J) {x : H} {Q : Subgroup H} (hQ : Ctl b x Q)
    (hxB : x ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hx1 : x ≠ 1) {u v g : H}
    (hu : u ∈ Subgroup.closure ({b, t} : Set H) ⊔ J)
    (hv : v ∈ Subgroup.closure ({b, t} : Set H) ⊔ J)
    (hux : u ∈ Nor (Subgroup.zpowers x)) (hg : g ∈ Nor (Subgroup.zpowers x))
    (hgu : g * u * g⁻¹ = v) :
    ∃ r ∈ Subgroup.closure ({b, t} : Set H) ⊔ J, r ∈ Nor (Subgroup.zpowers x) ∧
      v = r * u * r⁻¹ := by
  classical
  set K : Subgroup H := Opp 3 (Nor (Subgroup.zpowers b)) with hK
  have hxJ : x ∈ J := h.B₁_le_J hxB
  have hKx : K ≤ Nor (Subgroup.zpowers x) := fun κ hκ =>
    fs79_cen_le_nor_zpowers x (Subgroup.mem_centralizer_singleton_iff.mpr (h.K_comm_J hκ hxJ))
  obtain ⟨q, hq, n, hn, rfl⟩ := hQ.decomp g hg
  have hnN : n ∈ Nor (Subgroup.zpowers b) := hn.1
  have hnX : n ∈ Nor (Subgroup.zpowers x) := hn.2
  obtain ⟨hrM, hκ⟩ := h.rho_spec hnN
  set r : H := h.rho n with hr
  set κ : H := n * r⁻¹ with hκdef
  have hκx : κ ∈ Nor (Subgroup.zpowers x) := hKx hκ
  have hrx : r ∈ Nor (Subgroup.zpowers x) := by
    have : r = κ⁻¹ * n := by rw [hκdef]; group
    rw [this]
    exact (Nor (Subgroup.zpowers x)).mul_mem ((Nor (Subgroup.zpowers x)).inv_mem hκx) hnX
  set M₀ : Subgroup H := Subgroup.closure ({b, t} : Set H) ⊔ J with hM₀
  set u' : H := r * u * r⁻¹ with hu'
  have hu'M : u' ∈ M₀ := M₀.mul_mem (M₀.mul_mem hrM hu) (M₀.inv_mem hrM)
  have hu'x : u' ∈ Nor (Subgroup.zpowers x) :=
    (Nor (Subgroup.zpowers x)).mul_mem ((Nor (Subgroup.zpowers x)).mul_mem hrx hux)
      ((Nor (Subgroup.zpowers x)).inv_mem hrx)
  have hu'N : u'⁻¹ ∈ Nor (Subgroup.zpowers b) :=
    (Nor (Subgroup.zpowers b)).inv_mem (h.M0_le_Nor hu'M)
  have hw : u'⁻¹ * v ∈ K ⊔ Q := by
    have hn_eq : n = κ * r := by rw [hκdef]; group
    have e : u'⁻¹ * v = (u'⁻¹ * q * u') * (u'⁻¹ * κ * u') * κ⁻¹ * q⁻¹ := by
      rw [← hgu, hn_eq, hu']
      group
    rw [e]
    have h1 : u'⁻¹ * q * u' ∈ Q := by
      have := hQ.norm u'⁻¹ ((Nor (Subgroup.zpowers x)).inv_mem hu'x) q hq
      simpa using this
    have h2 : u'⁻¹ * κ * u' ∈ K := by
      have := L14.Opp_conj_mem hu'N hκ
      simpa using this
    have h3 : κ⁻¹ ∈ K := K.inv_mem hκ
    have h4 : q⁻¹ ∈ Q := Q.inv_mem hq
    exact (K ⊔ Q).mul_mem ((K ⊔ Q).mul_mem ((K ⊔ Q).mul_mem
      (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)) (Subgroup.mem_sup_left h3))
      (Subgroup.mem_sup_right h4)
  have hw1 : u'⁻¹ * v = 1 :=
    hQ.eq_one_of_mem_M0 h hxB hx1 (M₀.mul_mem (M₀.inv_mem hu'M) hv) hw
  refine ⟨r, hrM, hrx, ?_⟩
  have : v = u' := by
    calc v = u' * (u'⁻¹ * v) := by group
      _ = u' := by rw [hw1, mul_one]
  exact this

theorem Ctl.conj_YJ (h : FS79Hyp b t b₁ b₂ J) {x : H} {Q : Subgroup H} (hQ : Ctl b x Q)
    (hxB : x ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hx1 : x ≠ 1) {y₀ y₁ j₀ j₁ g : H}
    (hy₀ : y₀ ∈ Subgroup.closure ({b, t} : Set H)) (hy₁ : y₁ ∈ Subgroup.closure ({b, t} : Set H))
    (hj₀ : j₀ ∈ J) (hj₁ : j₁ ∈ J) (hux : y₀ * j₀ ∈ Nor (Subgroup.zpowers x))
    (hg : g ∈ Nor (Subgroup.zpowers x)) (hgu : g * (y₀ * j₀) * g⁻¹ = y₁ * j₁) :
    ∃ y ∈ Subgroup.closure ({b, t} : Set H), ∃ j ∈ J,
      y₁ = y * y₀ * y⁻¹ ∧ j₁ = j * j₀ * j⁻¹ := by
  have hu : y₀ * j₀ ∈ Subgroup.closure ({b, t} : Set H) ⊔ J := Subgroup.mul_mem_sup hy₀ hj₀
  have hv : y₁ * j₁ ∈ Subgroup.closure ({b, t} : Set H) ⊔ J := Subgroup.mul_mem_sup hy₁ hj₁
  obtain ⟨r, hrM, -, hvr⟩ := hQ.conj_in_M0 h hxB hx1 hu hv hux hg hgu
  obtain ⟨y, hy, j, hj, rfl⟩ := (CFSG.mem_sup_of_commute
    (A := Subgroup.closure ({b, t} : Set H)) (B := J)
    (fun a ha c hc => h.Y_comm_J ha hc)).mp hrM
  have hjy₀ : y₀ * j = j * y₀ := h.Y_comm_J hy₀ hj
  have hjj₀ : j * j₀ * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj hj₀) (J.inv_mem hj)
  have hyc : y * (j * j₀ * j⁻¹) = (j * j₀ * j⁻¹) * y := h.Y_comm_J hy hjj₀
  have e : y₁ * j₁ = (y * y₀ * y⁻¹) * (j * j₀ * j⁻¹) := by
    rw [hvr]
    calc y * j * (y₀ * j₀) * (y * j)⁻¹ = y * (j * y₀) * (j₀ * j⁻¹) * y⁻¹ := by group
      _ = y * (y₀ * j) * (j₀ * j⁻¹) * y⁻¹ := by rw [← hjy₀]
      _ = y * y₀ * (j * j₀ * j⁻¹) * y⁻¹ := by group
      _ = y * y₀ * ((j * j₀ * j⁻¹) * y⁻¹ * y) * y⁻¹ := by group
      _ = y * y₀ * (y⁻¹ * (y * (j * j₀ * j⁻¹))) * y⁻¹ := by group
      _ = y * y₀ * (y⁻¹ * ((j * j₀ * j⁻¹) * y)) * y⁻¹ := by rw [hyc]
      _ = (y * y₀ * y⁻¹) * (j * j₀ * j⁻¹) := by group
  have hYa : y * y₀ * y⁻¹ ∈ Subgroup.closure ({b, t} : Set H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hy₀) (Subgroup.inv_mem _ hy)
  have hmem : (y * y₀ * y⁻¹)⁻¹ * y₁ ∈ Subgroup.closure ({b, t} : Set H) ⊓ J := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hYa) hy₁, ?_⟩
    have : (y * y₀ * y⁻¹)⁻¹ * y₁ = (j * j₀ * j⁻¹) * j₁⁻¹ := by
      calc (y * y₀ * y⁻¹)⁻¹ * y₁ = (y * y₀ * y⁻¹)⁻¹ * (y₁ * j₁) * j₁⁻¹ := by group
        _ = (y * y₀ * y⁻¹)⁻¹ * ((y * y₀ * y⁻¹) * (j * j₀ * j⁻¹)) * j₁⁻¹ := by rw [e]
        _ = (j * j₀ * j⁻¹) * j₁⁻¹ := by group
    rw [this]
    exact J.mul_mem hjj₀ (J.inv_mem hj₁)
  rw [h.bt_inf_J, Subgroup.mem_bot] at hmem
  have hy1 : y₁ = y * y₀ * y⁻¹ := (inv_mul_eq_one.mp hmem).symm
  refine ⟨y, hy, j, hj, hy1, ?_⟩
  rw [hy1] at e
  exact mul_left_cancel e

end CFSG.RankThree.PartTwo.Sec21.FF81
