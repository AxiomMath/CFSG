module

public import CFSG.Quasithin.H13.A6S13828i

public section

namespace CFSG.Quasithin.H13.A6

open Matrix Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem exists_fixed_coset {G : Type*} [Group G] [Finite G] {P X A : Subgroup G}
    (hP : IsPGroup 2 P) (hX : IsPGroup 2 X) (hAX : A < X)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hPA : P ≤ Subgroup.normalizer (A : Set G)) :
    ∃ x ∈ X, x ∉ A ∧ ∀ p ∈ P, x⁻¹ * (p * x * p⁻¹) ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' := A.subgroupOf X with hA'
  have hcX : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X := fun p hp x hx =>
    (Subgroup.mem_normalizer_iff.mp (hPX hp) x).mp hx
  have hcA : ∀ p ∈ P, ∀ x ∈ A, p * x * p⁻¹ ∈ A := fun p hp x hx =>
    (Subgroup.mem_normalizer_iff.mp (hPA hp) x).mp hx
  let f : ↥P → ↥X → ↥X := fun p x => ⟨p * x * (p : G)⁻¹, hcX p p.2 x x.2⟩
  have hf : ∀ (p : ↥P) (x y : ↥X), x⁻¹ * y ∈ A' → (f p x)⁻¹ * f p y ∈ A' := by
    intro p x y h
    rw [Subgroup.mem_subgroupOf] at h ⊢
    have e : (((f p x)⁻¹ * f p y : ↥X) : G) = p * ((x : G)⁻¹ * y) * (p : G)⁻¹ := by
      simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hcA p p.2 _ (by simpa using h)
  let _ : MulAction ↥P (↥X ⧸ A') :=
    { smul := fun p => Quotient.map' (f p) fun x y h => by
        rw [QuotientGroup.leftRel_apply] at h ⊢
        exact hf p x y h
      one_smul := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          show (Quotient.mk'' (f 1 x) : ↥X ⧸ A') = Quotient.mk'' x
          congr 1
          exact Subtype.ext (by simp [f])
      mul_smul := fun p p' q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          show (Quotient.mk'' (f (p * p') x) : ↥X ⧸ A') = Quotient.mk'' (f p (f p' x))
          congr 1
          exact Subtype.ext (by simp only [f, Subgroup.coe_mul]; group) }
  have hsmul : ∀ (p : ↥P) (x : ↥X), p • (x : ↥X ⧸ A') = ((f p x : ↥X) : ↥X ⧸ A') :=
    fun _ _ => rfl
  have hidx : 2 ∣ Nat.card (↥X ⧸ A') := by
    have h1 : A'.index ≠ 1 := by
      intro h
      apply hAX.ne
      apply le_antisymm hAX.le
      intro x hx
      have := Subgroup.index_eq_one.mp h
      have hx' : (⟨x, hx⟩ : ↥X) ∈ A' := by rw [this]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    have h2 : A'.index ∣ Nat.card ↥X := A'.index_dvd_card
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    rw [hn] at h2
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h1 (by simpa using hk')
    rw [show Nat.card (↥X ⧸ A') = A'.index from rfl, hk']
    exact dvd_pow_self 2 hk0
  have hmod := hP.card_modEq_card_fixedPoints (↥X ⧸ A')
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints ↥P (↥X ⧸ A')) :=
    (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 hidx))
  have h1mem : ((1 : ↥X) : ↥X ⧸ A') ∈ MulAction.fixedPoints ↥P (↥X ⧸ A') := by
    intro p
    rw [hsmul]
    congr 1
    exact Subtype.ext (by simp [f])
  have hgt : 1 < Nat.card (MulAction.fixedPoints ↥P (↥X ⧸ A')) := by
    have : Nonempty (MulAction.fixedPoints ↥P (↥X ⧸ A')) := ⟨⟨_, h1mem⟩⟩
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥P (↥X ⧸ A')) := Nat.card_pos
    have := Nat.le_of_dvd hpos hfix
    omega
  have hnt := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨⟨q, hq⟩, hq1⟩ := exists_ne (⟨_, h1mem⟩ : MulAction.fixedPoints ↥P (↥X ⧸ A'))
  induction q using Quotient.inductionOn' with
  | h x =>
    refine ⟨x, x.2, fun hxA => hq1 (Subtype.ext ?_), fun p hp => ?_⟩
    · show (Quotient.mk'' x : ↥X ⧸ A') = ((1 : ↥X) : ↥X ⧸ A')
      have hx' : x ∈ A' := Subgroup.mem_subgroupOf.2 hxA
      exact QuotientGroup.eq.2 (by rw [mul_one]; exact A'.inv_mem hx')
    · have h2 := hq ⟨p, hp⟩
      rw [hsmul] at h2
      have h3 := QuotientGroup.eq.1 h2
      rw [Subgroup.mem_subgroupOf] at h3
      have e : (((f ⟨p, hp⟩ x)⁻¹ * x : ↥X) : G) = (p * x * p⁻¹)⁻¹ * x := by simp [f]
      rw [e] at h3
      have h4 := A.inv_mem h3
      simpa [mul_assoc] using h4

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}
  {γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)} {g c : G}

local notation "UL" => conjClosure (conjClosure S.V3 S.G1) L

@[expose] def nrm3 (c u : G) : G := u * (c * u * c⁻¹) * (c * c * u * (c * c)⁻¹)

omit [Finite G] in
theorem nrm3_conj (c l u : G) : nrm3 c (l * u * l⁻¹) = l * nrm3 (l⁻¹ * c * l) u * l⁻¹ := by
  simp only [nrm3]
  group

theorem UH_comm (D : S.LineData ρ β) :
    ∀ a ∈ conjClosure S.V3 S.G1, ∀ b ∈ conjClosure S.V3 S.G1, a * b = b * a := by
  intro a ha b hb
  have := D.hF.F911_3
  exact congrArg Subtype.val (this.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem nrm3_mem_V3 (D : S.LineData ρ β) {c' : G}
    (hc' : c' ∈ l0 L) (hc3 : c' ^ 3 = 1) (hc1 : c' ≠ 1) {u : G}
    (hu : u ∈ conjClosure S.V3 S.G1) : nrm3 c' u ∈ S.V3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcG1 : c' ∈ S.G1 := (le_sup_left.trans D.hF.toHypF91.L₁T_le_H) (S.l0_le_L1 hc')
  have hcV : c' ∈ Subgroup.centralizer (V : Set G) := S.o2Z_le_centralizer (oTwoRes_le _ hc')
  have hcU : ∀ x ∈ conjClosure S.V3 S.G1, c' * x * c'⁻¹ ∈ conjClosure S.V3 S.G1 := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hcG1) x).mp hx
  have h1 := hcU u hu
  have h2 : c' * c' * u * (c' * c')⁻¹ ∈ conjClosure S.V3 S.G1 := by
    have := hcU _ h1
    rwa [show c' * (c' * u * c'⁻¹) * c'⁻¹ = c' * c' * u * (c' * c')⁻¹ by group] at this
  have hNU : nrm3 c' u ∈ conjClosure S.V3 S.G1 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hu h1) h2
  have hc3' : c' * c' * c' = 1 := by rw [← pow_three']; exact hc3
  have hfix : c' * nrm3 c' u * c'⁻¹ = nrm3 c' u := by
    have e1 : c' * (c' * c' * u * (c' * c')⁻¹) * c'⁻¹ = u := by
      calc c' * (c' * c' * u * (c' * c')⁻¹) * c'⁻¹ = (c' * c' * c') * u * (c' * c' * c')⁻¹ := by
            group
        _ = u := by rw [hc3']; group
    calc c' * nrm3 c' u * c'⁻¹
        = (c' * u * c'⁻¹) * (c' * c' * u * (c' * c')⁻¹) *
            (c' * (c' * c' * u * (c' * c')⁻¹) * c'⁻¹) := by simp only [nrm3]; group
      _ = (c' * u * c'⁻¹) * (c' * c' * u * (c' * c')⁻¹) * u := by rw [e1]
      _ = nrm3 c' u := by
          simp only [nrm3]
          rw [S.UH_comm D _ (Subgroup.mul_mem _ h1 h2) _ hu]
          group
  set cH : ↥S.G1 := ⟨c', hcG1⟩ with hcH
  have hβN := D.hβe cH ⟨_, hNU⟩ ⟨_, hNU⟩ hfix.symm
  change S.bv β ⟨_, hNU⟩ = S.rv ρ cH (S.bv β ⟨_, hNU⟩) at hβN
  have hfw : ∀ w ∈ S.V3, ∀ hw : w ∈ conjClosure S.V3 S.G1,
      S.rv ρ cH (S.bv β ⟨w, hw⟩) = S.bv β ⟨w, hw⟩ := by
    intro w hw3 hw
    have hcw : c' * w * c'⁻¹ = w := by
      have := Subgroup.mem_centralizer_iff.mp hcV w (S.V3_le_V hw3)
      rw [← this, mul_inv_cancel_right]
    exact (D.hβe cH ⟨w, hw⟩ ⟨w, hw⟩ hcw.symm).symm
  have hρ3 : ρ cH ^ 3 = 1 := by
    rw [← map_pow]
    have : cH ^ 3 = 1 := Subtype.ext (by simpa [hcH] using hc3)
    rw [this, map_one]
  have hρ1 : ρ cH ≠ 1 := by
    intro h1
    have hQ := (D.hker cH).1 h1
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 S.G1) ⟨c', hQ⟩
    have hk' : c' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    apply hc1
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hc3)
      (orderOf_dvd_of_pow_eq_one hk')
  have hspan := fix_mem_span (S.pl_w1_w2_ne_zero D.hβk) (hfw _ S.u1_mem_V3 _)
    (hfw _ S.u2_mem_V3 _) hρ3 hρ1 hβN.symm
  rcases hspan with h | h | h | h
  · exact S.mem_V3_of_bv D.hβk ⟨_, hNU⟩ (s₁ := 0) (s₂ := 0) (by rw [h]; simp)
  · exact S.mem_V3_of_bv D.hβk ⟨_, hNU⟩ (s₁ := 1) (s₂ := 0) (by rw [h]; simp [w1])
  · exact S.mem_V3_of_bv D.hβk ⟨_, hNU⟩ (s₁ := 0) (s₂ := 1) (by rw [h]; simp [w2])
  · exact S.mem_V3_of_bv D.hβk ⟨_, hNU⟩ (s₁ := 1) (s₂ := 1) (by rw [h]; simp [w1, w2])

@[reducible] def commGrpOf {G : Type*} [Group G] (K : Subgroup G)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : CommGroup ↥K :=
  { (inferInstance : Group ↥K) with mul_comm := fun x y => Subtype.ext (hK x x.2 y y.2) }

theorem rearr6 {G : Type*} [Group G] {K : Subgroup G} (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    {a b c d e f : G} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K) (he : e ∈ K)
    (hf : f ∈ K) : a * b * (c * d) * (e * f) = a * c * e * (b * d * f) := by
  let _ := commGrpOf K hK
  have h : (⟨a, ha⟩ : ↥K) * ⟨b, hb⟩ * (⟨c, hc⟩ * ⟨d, hd⟩) * (⟨e, he⟩ * ⟨f, hf⟩) =
      ⟨a, ha⟩ * ⟨c, hc⟩ * ⟨e, he⟩ * (⟨b, hb⟩ * ⟨d, hd⟩ * ⟨f, hf⟩) := by ac_rfl
  exact congrArg Subtype.val h

theorem inv3 {G : Type*} [Group G] {K : Subgroup G} (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    {a b c : G} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) : (a * b * c)⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ := by
  let _ := commGrpOf K hK
  have h : ((⟨a, ha⟩ : ↥K) * ⟨b, hb⟩ * ⟨c, hc⟩)⁻¹ =
      (⟨a, ha⟩ : ↥K)⁻¹ * (⟨b, hb⟩)⁻¹ * (⟨c, hc⟩)⁻¹ := by
    rw [mul_inv, mul_inv]
  exact congrArg Subtype.val h

theorem rearr_nrm {G : Type*} [Group G] {K : Subgroup G} (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    {x a a' : G} (hx : x ∈ K) (ha : a ∈ K) (ha' : a' ∈ K) :
    x * (a * x) * (a' * (a * x)) = (x * x) * (x * (a' * (a * a))) := by
  let _ := commGrpOf K hK
  have h : (⟨x, hx⟩ : ↥K) * (⟨a, ha⟩ * ⟨x, hx⟩) * (⟨a', ha'⟩ * (⟨a, ha⟩ * ⟨x, hx⟩)) =
      (⟨x, hx⟩ * ⟨x, hx⟩) * (⟨x, hx⟩ * (⟨a', ha'⟩ * (⟨a, ha⟩ * ⟨a, ha⟩))) := by ac_rfl
  exact congrArg Subtype.val h

section Norm

variable [IsMulCommutative ↥(conjClosure V S.G1)]

theorem UL_sq (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    ∀ x ∈ UL, x * x = 1 := by
  have hcomm := S.UL_comm D hg hc hγ hΘ
  have hU2 : ∀ u ∈ conjClosure S.V3 S.G1, u * u = 1 := fun u hu => by
    rw [← sq]
    exact D.hF.F911_3.2 u hu
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, -, u, hu, rfl⟩ := hy
    calc l * u * l⁻¹ * (l * u * l⁻¹) = l * (u * u) * l⁻¹ := by group
      _ = 1 := by rw [hU2 u hu]; group
  | one => exact mul_one 1
  | mul y z hy hz ihy ihz =>
    have e : y * z = z * y := (Subgroup.mem_centralizer_iff.mp (hcomm hy) z hz).symm
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← e]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [ihy, ihz, one_mul]
  | inv y hy ihy =>
    calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
      _ = 1 := by rw [ihy, inv_one]

theorem nrm3_mem_V (D : S.LineData ρ β) (hg : S.GData g)
    (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) {c₀ : G}
    (hc₀ : c₀ ∈ l0 L) (hc₀3 : c₀ ^ 3 = 1) (hc₀1 : c₀ ≠ 1) : ∀ x ∈ UL, nrm3 c₀ x ∈ V := by
  have hcomm := S.UL_comm D hg hc hγ hΘ
  have hc₀L : c₀ ∈ L := l0_le_L hc₀
  have hcUL : ∀ x ∈ UL, c₀ * x * c₀⁻¹ ∈ UL := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L hc₀L) x).mp hx
  have hcUL2 : ∀ x ∈ UL, c₀ * c₀ * x * (c₀ * c₀)⁻¹ ∈ UL := fun x hx => by
    have := hcUL _ (hcUL x hx)
    rwa [show c₀ * (c₀ * x * c₀⁻¹) * c₀⁻¹ = c₀ * c₀ * x * (c₀ * c₀)⁻¹ by group] at this
  have hK : ∀ a ∈ UL, ∀ b ∈ UL, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hcomm ha) b hb).symm
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl, u, hu, rfl⟩ := hy
    rw [nrm3_conj]
    have hc' : l⁻¹ * c₀ * l ∈ l0 L := by
      have := (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_l0 (L.inv_mem hl)) c₀).mp hc₀
      simpa using this
    have hc'3 : (l⁻¹ * c₀ * l) ^ 3 = 1 := by
      rw [show (l⁻¹ * c₀ * l) ^ 3 = l⁻¹ * c₀ ^ 3 * l by
        rw [pow_three', pow_three']; group, hc₀3]
      group
    have hc'1 : l⁻¹ * c₀ * l ≠ 1 := by
      intro h1
      apply hc₀1
      calc c₀ = l * (l⁻¹ * c₀ * l) * l⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h3 := S.nrm3_mem_V3 D hc' hc'3 hc'1 hu
    exact (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl) _).mp (S.V3_le_V h3)
  | one => simp [nrm3]
  | mul y z hy hz ihy ihz =>
    have e : nrm3 c₀ (y * z) = nrm3 c₀ y * nrm3 c₀ z := by
      have e1 : nrm3 c₀ (y * z) = y * z * ((c₀ * y * c₀⁻¹) * (c₀ * z * c₀⁻¹)) *
          ((c₀ * c₀ * y * (c₀ * c₀)⁻¹) * (c₀ * c₀ * z * (c₀ * c₀)⁻¹)) := by
        simp only [nrm3]
        group
      rw [e1, rearr6 hK hy hz (hcUL y hy) (hcUL z hz) (hcUL2 y hy) (hcUL2 z hz)]
      simp only [nrm3]
    rw [e]
    exact V.mul_mem ihy ihz
  | inv y hy ihy =>
    have e : nrm3 c₀ y⁻¹ = (nrm3 c₀ y)⁻¹ := by
      have e1 : nrm3 c₀ y⁻¹ = y⁻¹ * (c₀ * y * c₀⁻¹)⁻¹ * (c₀ * c₀ * y * (c₀ * c₀)⁻¹)⁻¹ := by
        simp only [nrm3]
        group
      rw [e1, nrm3, inv3 hK hy (hcUL y hy) (hcUL2 y hy)]
    rw [e]
    exact V.inv_mem ihy

theorem le_of_comm_mem (D : S.LineData ρ β) (hg : S.GData g)
    (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) {c₀ : G}
    (hc₀ : c₀ ∈ l0 L) (hc₀3 : c₀ ^ 3 = 1) (hc₀1 : c₀ ≠ 1) {A X : Subgroup G} (hVA : V ≤ A)
    (hXU : X ≤ UL) (hAU : A ≤ UL) (hcA : c₀ ∈ Subgroup.normalizer (A : Set G))
    (hcomm : ∀ x ∈ X, c₀ * x * c₀⁻¹ * x⁻¹ ∈ A) : X ≤ A := by
  have hcm := S.UL_comm D hg hc hγ hΘ
  have hK : ∀ a ∈ UL, ∀ b ∈ UL, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hcm ha) b hb).symm
  have hsq := S.UL_sq D hg hc hγ hΘ
  intro x hx
  set a := c₀ * x * c₀⁻¹ * x⁻¹ with ha
  have haA : a ∈ A := hcomm x hx
  have ha' : c₀ * a * c₀⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hcA a).mp haA
  have hxU := hXU hx
  have e1 : c₀ * x * c₀⁻¹ = a * x := by rw [ha]; group
  have e2 : c₀ * c₀ * x * (c₀ * c₀)⁻¹ = (c₀ * a * c₀⁻¹) * (a * x) := by
    calc c₀ * c₀ * x * (c₀ * c₀)⁻¹ = c₀ * (c₀ * x * c₀⁻¹) * c₀⁻¹ := by group
      _ = c₀ * (a * x) * c₀⁻¹ := by rw [e1]
      _ = (c₀ * a * c₀⁻¹) * (c₀ * x * c₀⁻¹) := by group
      _ = (c₀ * a * c₀⁻¹) * (a * x) := by rw [e1]
  have hN := S.nrm3_mem_V D hg hc hγ hΘ hc₀ hc₀3 hc₀1 x hxU
  have e3 : nrm3 c₀ x = x * ((c₀ * a * c₀⁻¹) * (a * a)) := by
    simp only [nrm3]
    rw [e1, e2, rearr_nrm hK hxU (hAU haA) (hAU ha'), hsq x hxU, one_mul]
  have hx' : x = nrm3 c₀ x * ((c₀ * a * c₀⁻¹) * (a * a))⁻¹ := by
    rw [e3]
    group
  rw [hx']
  exact A.mul_mem (hVA hN) (A.inv_mem (A.mul_mem ha' (A.mul_mem haA haA)))

end Norm

theorem rearr4 {G : Type*} [Group G] {K : Subgroup G} (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    {x y a b : G} (hx : x ∈ K) (hy : y ∈ K) (ha : a ∈ K) (hb : b ∈ K) :
    (x * y)⁻¹ * (a * b) = (x⁻¹ * a) * (y⁻¹ * b) := by
  let _ := commGrpOf K hK
  have h : ((⟨x, hx⟩ : ↥K) * ⟨y, hy⟩)⁻¹ * (⟨a, ha⟩ * ⟨b, hb⟩) =
      ((⟨x, hx⟩ : ↥K)⁻¹ * ⟨a, ha⟩) * ((⟨y, hy⟩ : ↥K)⁻¹ * ⟨b, hb⟩) := by
    rw [mul_inv]
    ac_rfl
  exact congrArg Subtype.val h

theorem inv_rearr {G : Type*} [Group G] {K : Subgroup G} (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    {x a : G} (hx : x ∈ K) (ha : a ∈ K) : (x⁻¹)⁻¹ * a⁻¹ = (x⁻¹ * a)⁻¹ := by
  rw [inv_inv, _root_.mul_inv_rev, inv_inv]
  exact hK _ hx _ (K.inv_mem ha)

section Chief

variable [IsMulCommutative ↥(conjClosure V S.G1)]

theorem isPGroup_UL (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c) (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) : IsPGroup 2 ↥UL :=
  fun x => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; simpa using S.UL_sq D hg hc hγ hΘ x x.2)⟩

theorem pCore_comm_mem (D : S.LineData ρ β) (hg : S.GData g) (hc : S.CData c)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) {A X : Subgroup G}
    (hAX : A < X) (hXU : X ≤ UL) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hirr : ∀ W' : Subgroup G, A ≤ W' → W' ≤ X → L ≤ Subgroup.normalizer (W' : Set G) →
      W' = A ∨ W' = X) :
    ∀ p ∈ pCoreOf 2 L, ∀ x ∈ X, p * x * p⁻¹ * x⁻¹ ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcm := S.UL_comm D hg hc hγ hΘ
  have hK : ∀ a ∈ UL, ∀ b ∈ UL, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hcm ha) b hb).symm
  set P := pCoreOf 2 L with hP
  have hPL : P ≤ L := pCoreOf_le 2 L
  have hcX : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X := fun l hl x hx =>
    (Subgroup.mem_normalizer_iff.mp (hLX hl) x).mp hx
  have hcA : ∀ l ∈ L, ∀ x ∈ A, l * x * l⁻¹ ∈ A := fun l hl x hx =>
    (Subgroup.mem_normalizer_iff.mp (hLA hl) x).mp hx
  have hX2 : IsPGroup 2 ↥X := (S.isPGroup_UL D hg hc hγ hΘ).to_le hXU
  obtain ⟨x₀, hx₀X, hx₀A, hx₀⟩ := exists_fixed_coset (pCoreOf_isPGroup 2 L) hX2 hAX
    (hPL.trans hLX) (hPL.trans hLA)
  let Y : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ∀ p ∈ P, x⁻¹ * (p * x * p⁻¹) ∈ A}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨X.mul_mem hx.1 hy.1, fun p hp => ?_⟩
        have e : p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) := by group
        rw [e, rearr4 hK (hXU hx.1) (hXU hy.1) (hXU (hcX p (hPL hp) x hx.1))
          (hXU (hcX p (hPL hp) y hy.1))]
        exact A.mul_mem (hx.2 p hp) (hy.2 p hp)
      one_mem' := ⟨X.one_mem, fun p _ => by simp⟩
      inv_mem' := fun {x} hx => by
        refine ⟨X.inv_mem hx.1, fun p hp => ?_⟩
        have e : p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ := by group
        rw [e, inv_rearr hK (hXU hx.1) (hXU (hcX p (hPL hp) x hx.1))]
        exact A.inv_mem (hx.2 p hp) }
  have hAY : A ≤ Y := fun x hx => ⟨hAX.le hx, fun p hp =>
    A.mul_mem (A.inv_mem hx) (hcA p (hPL hp) x hx)⟩
  have hYX : Y ≤ X := fun x hx => hx.1
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    have key : ∀ l ∈ L, ∀ x ∈ Y, l * x * l⁻¹ ∈ Y := by
      intro l hl x hx
      refine ⟨hcX l hl x hx.1, fun p hp => ?_⟩
      have hp' : l⁻¹ * p * l ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (L.inv_mem hl)) p).mp hp
        simpa using this
      have e : (l * x * l⁻¹)⁻¹ * (p * (l * x * l⁻¹) * p⁻¹) =
          l * (x⁻¹ * ((l⁻¹ * p * l) * x * (l⁻¹ * p * l)⁻¹)) * l⁻¹ := by group
      rw [e]
      exact hcA l hl _ (hx.2 _ hp')
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key l hl x
    · intro hx
      have := key l⁻¹ (L.inv_mem hl) _ hx
      simpa [mul_assoc] using this
  have hY : Y = X := by
    rcases hirr Y hAY hYX hLY with h | h
    · exact absurd (h ▸ (⟨hx₀X, hx₀⟩ : x₀ ∈ Y)) hx₀A
    · exact h
  intro p hp x hx
  have hxY : x ∈ Y := hY ▸ hx
  have hb := hxY.2 p hp
  have e : p * x * p⁻¹ * x⁻¹ = x⁻¹ * (p * x * p⁻¹) := by
    have h1 := hK x (hXU hx) _ (hXU (hcX p (hPL hp) x hx))
    calc p * x * p⁻¹ * x⁻¹ = x⁻¹ * (x * (p * x * p⁻¹)) * x⁻¹ := by group
      _ = x⁻¹ * ((p * x * p⁻¹) * x) * x⁻¹ := by rw [h1]
      _ = x⁻¹ * (p * x * p⁻¹) := by group
  rw [e]
  exact hb

end Chief

theorem exists_chief {X : Subgroup G} (hVX : V < X) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ∃ A : Subgroup G, V ≤ A ∧ A < X ∧ L ≤ Subgroup.normalizer (A : Set G) ∧
      ∀ W' : Subgroup G, A ≤ W' → W' ≤ X → L ≤ Subgroup.normalizer (W' : Set G) →
        W' = A ∨ W' = X := by
  let F := {K : Subgroup G // V ≤ K ∧ K < X ∧ L ≤ Subgroup.normalizer (K : Set G)}
  have : Finite (Subgroup G) := Finite.of_injective (fun K : Subgroup G => (K : Set G))
    SetLike.coe_injective
  have : Finite F := Finite.of_injective (fun K : F => K.1) Subtype.val_injective
  have : Nonempty F := ⟨⟨V, le_rfl, hVX, hLV⟩⟩
  obtain ⟨⟨A, hVA, hAX, hLA⟩, hmax⟩ := Finite.exists_max (fun K : F => Nat.card ↥K.1)
  refine ⟨A, hVA, hAX, hLA, fun W' hAW hWX hLW => ?_⟩
  by_cases hW : W' = X
  · exact Or.inr hW
  · left
    have h1 := hmax ⟨W', hVA.trans hAW, lt_of_le_of_ne hWX hW, hLW⟩
    exact (Subgroup.eq_of_le_of_card_ge hAW h1).symm

end Setting4

end CFSG.Quasithin.H13.A6

