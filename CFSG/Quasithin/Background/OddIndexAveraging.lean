module

public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin

open scoped Pointwise
open QuotientGroup

variable {G : Type*} [Group G]

theorem commutator_mem_and_sq_mem_of_fixed {H Q Z N : Subgroup G}
    (hZN : Z ≤ N) (hNQ : N ≤ Q) (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hQZ : Q ≤ Subgroup.normalizer (Z : Set G))
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ Z) (hNsq : ∀ a ∈ N, a * a ∈ Z)
    (hNQZ : ∀ a ∈ N, ∀ x ∈ Q, x * a * x⁻¹ * a⁻¹ ∈ Z)
    (htriv : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ N)
    (hfix : ∀ x ∈ Q, (∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ Z) → x ∈ Z) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ ∀ x ∈ Q, x * x ∈ Z := by
  classical
  have hZQ : Z ≤ Q := hZN.trans hNQ
  have hNQnorm : ∀ x ∈ Q, ∀ a ∈ N, x * a * x⁻¹ ∈ N := by
    intro x hx a ha
    have h := hNQZ a ha x hx
    have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact N.mul_mem (hZN h) ha
  have hQN : Q ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => hNQnorm x hx a ha
    · intro ha
      have h := hNQnorm x⁻¹ (Q.inv_mem hx) (x * a * x⁻¹) ha
      simpa [mul_assoc] using h
  have hLN : (N.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQN
  have hKN : (Z.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hNQ.trans hQZ)
  haveI : (N.subgroupOf Q).Normal := hLN
  haveI : (Z.subgroupOf N).Normal := hKN
  letI : IsMulCommutative (N ⧸ Z.subgroupOf N) := by
    refine IsMulCommutative.of_comm ?_
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have h := hNab (x : G) x.2 (y : G) y.2
    have h' : ((x * y / (y * x) : ↥N) : G) =
        (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
      group
    rw [h']
    exact h
  letI : CommGroup (N ⧸ Z.subgroupOf N) := IsMulCommutative.instCommGroup
  have hsqbar : ∀ a : N ⧸ Z.subgroupOf N, a * a = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hNsq (x : G) x.2
  let c : ↥Q → ↥H → N ⧸ Z.subgroupOf N := fun x h =>
    QuotientGroup.mk ⟨(h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹, htriv (h : G) h.2 (x : G) x.2⟩
  have hc_mul : ∀ (x y : ↥Q) (h : ↥H), c (x * y) h = c x h * c y h := by
    intro x y h
    let a : ↥N := ⟨(h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹, htriv (h : G) h.2 (x : G) x.2⟩
    let b : ↥N := ⟨(h : G) * (y : G) * (h : G)⁻¹ * (y : G)⁻¹, htriv (h : G) h.2 (y : G) y.2⟩
    let b' : ↥N := ⟨(x : G) * (b : G) * (x : G)⁻¹, hNQnorm (x : G) x.2 (b : G) b.2⟩
    have hb' : (b' : N ⧸ Z.subgroupOf N) = (b : N ⧸ Z.subgroupOf N) := by
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      have h := hNQZ (b : G) b.2 (x : G) x.2
      have h' : ((b' / b : ↥N) : G) =
          (x : G) * (b : G) * (x : G)⁻¹ * (b : G)⁻¹ := by
        simp only [b', b, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
      rw [h']
      exact h
    have hcxy : c (x * y) h = QuotientGroup.mk (a * b') := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp only [c, a, b', b, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    calc
      c (x * y) h = QuotientGroup.mk (a * b') := hcxy
      _ = QuotientGroup.mk a * QuotientGroup.mk b' := by
        rw [QuotientGroup.mk_mul]
      _ = QuotientGroup.mk a * QuotientGroup.mk b := by rw [hb']
      _ = c x h * c y h := rfl
  have hc_one : c 1 = 1 := by
    funext h
    have e :
        (⟨(h : G) * (1 : G) * (h : G)⁻¹ * (1 : G)⁻¹,
          htriv (h : G) h.2 (1 : G) Q.one_mem⟩ : ↥N) = 1 := by
      apply Subtype.ext
      simp
    change QuotientGroup.mk (⟨(h : G) * (1 : G) * (h : G)⁻¹ * (1 : G)⁻¹,
      htriv (h : G) h.2 (1 : G) Q.one_mem⟩ : ↥N) = 1
    rw [e]
    exact map_one (QuotientGroup.mk' (Z.subgroupOf N))
  have hc_inv : ∀ (x : ↥Q) (h : ↥H), c x⁻¹ h = (c x h)⁻¹ := by
    intro x h
    have h1 := hc_mul x x⁻¹ h
    rw [mul_inv_cancel, hc_one] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hc_comm : ∀ x y : ↥Q,
      c (⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹,
        Q.mul_mem (Q.mul_mem (Q.mul_mem x.2 y.2) (Q.inv_mem x.2)) (Q.inv_mem y.2)⟩ : ↥Q) = 1 := by
    intro x y
    funext h
    have hxy := hc_mul x y h
    have hix := hc_inv x h
    have hiy := hc_inv y h
    calc
      c (⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹,
          Q.mul_mem (Q.mul_mem (Q.mul_mem x.2 y.2) (Q.inv_mem x.2)) (Q.inv_mem y.2)⟩ : ↥Q) h
          = c (((x * y) * x⁻¹) * y⁻¹) h := rfl
      _ = c ((x * y) * x⁻¹) h * c y⁻¹ h := by rw [hc_mul]
      _ = (c (x * y) h * c x⁻¹ h) * c y⁻¹ h := by rw [hc_mul]
      _ = ((c x h * c y h) * (c x h)⁻¹) * (c y h)⁻¹ := by rw [hxy, hix, hiy]
      _ = 1 := by simp [mul_comm, mul_assoc]
  have hcommZ : ∀ x y : ↥Q,
      (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ Z := by
    intro x y
    let q : ↥Q := ⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹,
      Q.mul_mem (Q.mul_mem (Q.mul_mem x.2 y.2) (Q.inv_mem x.2)) (Q.inv_mem y.2)⟩
    apply hfix (q : G) q.2
    intro h hh
    have h1 : c q ⟨h, hh⟩ = 1 := congrFun (hc_comm x y) ⟨h, hh⟩
    have h2 := (QuotientGroup.eq_one_iff
      (⟨(h : G) * (q : G) * (h : G)⁻¹ * (q : G)⁻¹, htriv (h : G) hh (q : G) q.2⟩ : ↥N)).mp h1
    simpa [Subgroup.mem_subgroupOf, q] using h2
  have hsqZ : ∀ x : ↥Q, (x : G) * (x : G) ∈ Z := by
    intro x
    let q : ↥Q := x * x
    apply hfix (q : G) q.2
    intro h hh
    have h1 : c q ⟨h, hh⟩ = 1 := by
      dsimp only [q]
      rw [hc_mul, hsqbar]
    have h2 := (QuotientGroup.eq_one_iff
      (⟨(h : G) * (q : G) * (h : G)⁻¹ * (q : G)⁻¹, htriv (h : G) hh (q : G) q.2⟩ : ↥N)).mp h1
    simpa [Subgroup.mem_subgroupOf, q] using h2
  exact ⟨fun x hx y hy => hcommZ ⟨x, hx⟩ ⟨y, hy⟩,
    fun x hx => hsqZ ⟨x, hx⟩⟩

theorem mem_of_centralizerMod_odd {P T Q Z N : Subgroup G} [Finite G]
    (hTP : T ≤ P) (hodd : Odd (T.relIndex P))
    (hZN : Z ≤ N) (hNQ : N ≤ Q) (hPZ : P ≤ Subgroup.normalizer (Z : Set G))
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z) (hsq : ∀ x ∈ Q, x * x ∈ Z)
    (htriv : ∀ p ∈ P, ∀ x ∈ Q, p * x * p⁻¹ * x⁻¹ ∈ N)
    (hfix : ∀ x ∈ Q, (∀ p ∈ P, p * x * p⁻¹ * x⁻¹ ∈ Z) → x ∈ Z) :
    centralizerMod Z Q T ≤ N := by
  classical
  intro v hv
  rw [mem_centralizerMod] at hv
  obtain ⟨hvQ, _hvNZ, hvT⟩ := hv
  have hZQ : Z ≤ Q := hZN.trans hNQ
  have hKnormal : (Z.subgroupOf Q).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h := hab x hx z (hZQ hz)
      have e : x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
      rw [e]
      exact Z.mul_mem h hz
    · intro hz
      have h := hab x⁻¹ (Q.inv_mem hx) (x * z * x⁻¹) (hZQ hz)
      have e : z = (x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ * (x * z * x⁻¹)⁻¹) *
          (x * z * x⁻¹) := by group
      rw [e]
      exact Z.mul_mem h hz
  have hNnormalQ : ∀ x ∈ Q, ∀ a ∈ N, x * a * x⁻¹ ∈ N := by
    intro x hx a ha
    have h := hab x hx a (hNQ ha)
    have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact N.mul_mem (hZN h) ha
  have hLnormal : (N.subgroupOf Q).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => hNnormalQ x hx a ha
    · intro ha
      have h := hNnormalQ x⁻¹ (Q.inv_mem hx) (x * a * x⁻¹) ha
      simpa [mul_assoc] using h
  haveI : (Z.subgroupOf Q).Normal := hKnormal
  haveI : (N.subgroupOf Q).Normal := hLnormal
  letI : IsMulCommutative (Q ⧸ Z.subgroupOf Q) := by
    refine IsMulCommutative.of_comm ?_
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have h := hab (x : G) x.2 (y : G) y.2
    have h' : ((x * y / (y * x) : ↥Q) : G) =
        (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
      group
    rw [h']
    exact h
  letI : CommGroup (Q ⧸ Z.subgroupOf Q) := IsMulCommutative.instCommGroup
  have hsqbar : ∀ a : Q ⧸ Z.subgroupOf Q, a * a = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq (x : G) x.2
  let ρ : ↥P →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom (H := Q)).comp (Subgroup.inclusion hPQ)
  have hρ_apply : ∀ (p : ↥P) (q : ↥Q),
      ((ρ p) q : G) = (p : G) * (q : G) * (p : G)⁻¹ := by
    intro p q
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hρ_inv_apply : ∀ (p : ↥P) (q : ↥Q),
      (((ρ p).symm q : ↥Q) : G) = (p : G)⁻¹ * (q : G) * (p : G) := by
    intro p q
    rw [show (ρ p).symm = (ρ p)⁻¹ from rfl, ← map_inv ρ p]
    simpa using hρ_apply (p⁻¹) q
  have hKmap : ∀ p : ↥P, (Z.subgroupOf Q).map (ρ p).toMonoidHom = Z.subgroupOf Q := by
    intro p
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩
      change (k : G) ∈ Z at hk
      change (((ρ p) k : ↥Q) : G) ∈ Z
      have h := (Subgroup.mem_normalizer_iff.mp (hPZ p.2) (k : G)).mp hk
      simpa [hρ_apply p k] using h
    · intro hz
      refine ⟨((ρ p).symm) z, ?_, (ρ p).apply_symm_apply z⟩
      have hz' : (z : G) ∈ Z := by simpa [Subgroup.mem_subgroupOf] using hz
      have h := (Subgroup.mem_normalizer_iff.mp (hPZ (P.inv_mem p.2)) (z : G)).mp hz'
      simpa [Subgroup.mem_subgroupOf, hρ_inv_apply p z] using h
  let C := ↥P ⧸ T.subgroupOf P
  letI : Fintype C := Fintype.ofFinite C
  let rep : C → ↥P := fun c => Quotient.out c
  have hrep_mk : ∀ c : C, QuotientGroup.mk (rep c) = c := fun c => QuotientGroup.out_eq' c
  let conjQ : ↥P → ↥Q := fun x =>
    ⟨(x : G) * v * (x : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPQ x.2) v).mp hvQ⟩
  have hconjQ_apply : ∀ x : ↥P, (conjQ x : G) = (x : G) * v * (x : G)⁻¹ :=
    fun _ => rfl
  let F : C → Q ⧸ Z.subgroupOf Q := fun c => QuotientGroup.mk (conjQ (rep c))
  let σbar : Q ⧸ Z.subgroupOf Q := ∏ c : C, F c
  have hconj_rep : ∀ (c : C) (x : ↥P), QuotientGroup.mk x = c →
      QuotientGroup.mk (conjQ x) = F c := by
    intro c x hx
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (T.subgroupOf P) x
    rw [hx] at ht
    have hrep : (rep c : G) = (x : G) * (t : G) := congrArg Subtype.val ht
    have htfix : (t : G) * v * (t : G)⁻¹ * v⁻¹ ∈ Z := by
      have h := hvT (t : G) t.2
      have e : (t : G) * v * (t : G)⁻¹ * v⁻¹ =
          (v * (t : G) * v⁻¹ * (t : G)⁻¹)⁻¹ := by group
      rw [e]
      exact Z.inv_mem h
    have hz : (QuotientGroup.mk (conjQ (x * t)) : Q ⧸ Z.subgroupOf Q) =
        (QuotientGroup.mk (conjQ x) : Q ⧸ Z.subgroupOf Q) := by
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      have hxZ : (x : G) * ((t : G) * v * (t : G)⁻¹ * v⁻¹) * (x : G)⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hPZ x.2) _).mp htfix
      have h' : ((conjQ (x * t) / conjQ x : ↥Q) : G) =
          (x : G) * ((t : G) * v * (t : G)⁻¹ * v⁻¹) * (x : G)⁻¹ := by
        simp only [conjQ, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
          div_eq_mul_inv]
        group
      rw [h']
      exact hxZ
    have hFc : F c = QuotientGroup.mk (conjQ (x * t)) := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp only [conjQ, rep, Subgroup.coe_mul]
      rw [hrep]
    exact hz.symm.trans hFc.symm
  let e : ↥P → MulAut (Q ⧸ Z.subgroupOf Q) := fun p =>
    QuotientGroup.congr (Z.subgroupOf Q) (Z.subgroupOf Q) (ρ p) (hKmap p)
  have he_apply : ∀ (p : ↥P) (q : ↥Q),
      e p (QuotientGroup.mk q) = QuotientGroup.mk ((ρ p) q) := by
    intro p q
    exact QuotientGroup.congr_mk _ _ _ _ _
  have heF : ∀ (p : ↥P) (c : C), e p (F c) = F (p • c) := by
    intro p c
    let xq : ↥P := p * rep c
    have hxq : QuotientGroup.mk xq = p • c := by
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    have h1 : QuotientGroup.mk (conjQ xq) = F (p • c) := hconj_rep (p • c) xq hxq
    have h2 : e p (F c) = QuotientGroup.mk (conjQ xq) := by
      change e p (QuotientGroup.mk (conjQ (rep c))) = _
      rw [he_apply]
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp only [conjQ, xq, hρ_apply, Subgroup.coe_mul]
      group
    exact h2.trans h1
  have hσ_fixed : ∀ p : ↥P, e p σbar = σbar := by
    intro p
    have hprod : e p σbar = ∏ c : C, F (p • c) := by
      change e p (∏ c : C, F c) = ∏ c : C, F (p • c)
      rw [map_prod]
      exact Finset.prod_congr rfl fun c _ => heF p c
    calc
      e p σbar = ∏ c : C, F (p • c) := hprod
      _ = ∏ c : C, F c := by
        simpa only [MulAction.toPerm_apply] using
          (Equiv.prod_comp (MulAction.toPerm p) F)
      _ = σbar := rfl
  let s : ↥Q := Quotient.out σbar
  have hs_mk : QuotientGroup.mk s = σbar := QuotientGroup.out_eq' σbar
  have hs_fixed : ∀ p : ↥P, (p : G) * (s : G) * (p : G)⁻¹ * (s : G)⁻¹ ∈ Z := by
    intro p
    have h1 : e p (QuotientGroup.mk s) = QuotientGroup.mk s := by
      simpa [hs_mk] using hσ_fixed p
    rw [he_apply] at h1
    have h2 := (QuotientGroup.eq_iff_div_mem.mp h1)
    rw [Subgroup.mem_subgroupOf] at h2
    convert h2 using 1
    simp only [hρ_apply, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
      div_eq_mul_inv]
  have hsZ : (s : G) ∈ Z := by
    apply hfix (s : G) s.2
    intro p hp
    exact hs_fixed ⟨p, hp⟩
  have hσbar_one : σbar = 1 := by
    rw [← hs_mk]
    exact (QuotientGroup.eq_one_iff s).mpr (by simpa [Subgroup.mem_subgroupOf] using hsZ)
  letI : IsMulCommutative (Q ⧸ N.subgroupOf Q) := by
    refine IsMulCommutative.of_comm ?_
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have h := hab (x : G) x.2 (y : G) y.2
    have h' : ((x * y / (y * x) : ↥Q) : G) =
        (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
      group
    rw [h']
    exact hZN h
  letI : CommGroup (Q ⧸ N.subgroupOf Q) := IsMulCommutative.instCommGroup
  have hφwell : (Z.subgroupOf Q) ≤ (N.subgroupOf Q).comap (MonoidHom.id ↥Q) := by
    intro z hz
    exact hZN (by simpa [Subgroup.mem_subgroupOf] using hz)
  let φ : Q ⧸ Z.subgroupOf Q →* Q ⧸ N.subgroupOf Q :=
    QuotientGroup.map (Z.subgroupOf Q) (N.subgroupOf Q) (MonoidHom.id ↥Q) hφwell
  have hφσ : φ σbar = ∏ c : C, φ (F c) := by
    change φ (∏ c : C, F c) = ∏ c : C, φ (F c)
    rw [map_prod]
  have hφF : ∀ c : C, φ (F c) = QuotientGroup.mk (⟨v, hvQ⟩ : ↥Q) := by
    intro c
    have htrivc : (rep c : G) * v * (rep c : G)⁻¹ * v⁻¹ ∈ N :=
      htriv (rep c : G) (rep c).2 v hvQ
    have h' : ((conjQ (rep c) / (⟨v, hvQ⟩ : ↥Q) : ↥Q) : G) =
        (rep c : G) * v * (rep c : G)⁻¹ * v⁻¹ := by
      simp only [conjQ, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
        div_eq_mul_inv]
    have hmap : φ (QuotientGroup.mk (conjQ (rep c))) =
        QuotientGroup.mk (conjQ (rep c)) := by
      dsimp only [φ]
      simpa only [MonoidHom.id_apply] using
        (QuotientGroup.map_mk (N := Z.subgroupOf Q) (M := N.subgroupOf Q)
          (f := MonoidHom.id ↥Q) (h := hφwell) (x := conjQ (rep c)))
    rw [hmap]
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, h']
    exact htrivc
  have hφσ_pow : φ σbar =
      (QuotientGroup.mk (⟨v, hvQ⟩ : ↥Q) : Q ⧸ N.subgroupOf Q) ^ Fintype.card C := by
    rw [hφσ]
    simp_rw [hφF]
    rw [Finset.prod_const, Finset.card_univ]
  have hφσ_one : φ σbar = 1 := by
    rw [hσbar_one, map_one]
  have hcard : (T.subgroupOf P).index = Fintype.card C := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hoddC : Odd (Fintype.card C) := by
    simpa [Subgroup.relIndex, C, hcard] using hodd
  let a : Q ⧸ N.subgroupOf Q := QuotientGroup.mk (⟨v, hvQ⟩ : ↥Q)
  have ha2 : a * a = 1 := by
    change QuotientGroup.mk ((⟨v, hvQ⟩ : ↥Q) * (⟨v, hvQ⟩ : ↥Q)) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hZN (hsq v hvQ)
  have hapow : a ^ Fintype.card C = 1 := by
    rw [← hφσ_pow, hφσ_one]
  have ha_one : a = 1 := by
    obtain ⟨m, hm⟩ := hoddC
    have ha2' : a ^ 2 = 1 := by simpa [pow_two] using ha2
    have hpow : a ^ Fintype.card C = a := by
      rw [hm, pow_succ, pow_mul, ha2', one_pow, one_mul]
    rwa [hpow] at hapow
  have hvN : v ∈ N := by
    have hmem : (⟨v, hvQ⟩ : ↥Q) ∈ N.subgroupOf Q := (QuotientGroup.eq_one_iff _).mp ha_one
    simpa [Subgroup.mem_subgroupOf] using hmem
  exact hvN

end CFSG.Quasithin
