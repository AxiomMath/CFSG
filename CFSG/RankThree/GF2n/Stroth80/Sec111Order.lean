module

public import CFSG.RankThree.GF2n.Stroth80.Sec111Two
public import CFSG.RankThree.GF2n.Stroth80.Sec111Norm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem two_pow_mul_odd_of_hom {A U : Type} [Group A] [Finite A] [Group U] [Finite U]
    (C : Subgroup A) (lam : ↥C →* U) (N : ℕ) (hU : Nat.card U = N) (hN : Odd N)
    (hker : ∀ c : ↥C, lam c = 1 → ∃ k : ℕ, c ^ 2 ^ k = 1) :
    ∃ k m : ℕ, Odd m ∧ Nat.card ↥C = 2 ^ k * m ∧ m ∣ N := by
  have hP : IsPGroup 2 ↥lam.ker := by
    intro x
    obtain ⟨k, hk⟩ := hker x.1 (MonoidHom.mem_ker.mp x.2)
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have hmul : Nat.card ↥lam.ker * Nat.card ↥lam.range = Nat.card ↥C := by
    rw [← Subgroup.index_ker lam]
    exact Subgroup.card_mul_index lam.ker
  have hdvd : Nat.card ↥lam.range ∣ N := by
    rw [← hU]
    exact Subgroup.card_subgroup_dvd_card lam.range
  refine ⟨k, Nat.card ↥lam.range, hN.of_dvd_nat hdvd, ?_, hdvd⟩
  rw [← hmul, hk]

theorem H0_le_M : H0 M Z ≤ M := fun _ hx => hx.1

@[expose] def mkH (M Q Z : Subgroup G) [(Q.subgroupOf M).Normal] : ↥(H0 M Z) →* Mbar M Q :=
  (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion (H0_le_M : H0 M Z ≤ M))

theorem mkH_eq_one_iff [(Q.subgroupOf M).Normal] (g : ↥(H0 M Z)) :
    mkH M Q Z g = 1 ↔ (g : G) ∈ Q :=
  (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (⟨(g : G), H0_le_M g.2⟩ : ↥M)).trans
    Subgroup.mem_subgroupOf

theorem phi_eq_of_mkH_eq [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφ : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {g g' : ↥(H0 M Z)}
    (h : mkH M Q Z g = mkH M Q Z g') : φ g = φ g' := by
  have h1 : mkH M Q Z (g⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : φ (g⁻¹ * g') = 1 := (hφ (g⁻¹ * g')).mpr ((mkH_eq_one_iff (g⁻¹ * g')).mp h1)
  calc φ g = φ g * φ (g⁻¹ * g') := by rw [h2, mul_one]
    _ = φ g' := by rw [← map_mul, mul_inv_cancel_left]

@[expose] noncomputable def liftF [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) (c : Mbar M Q) :
    M₀.E ≃ₗ[K] M₀.E :=
  φ (Function.invFun (mkH M Q Z) c)

theorem liftF_mkH [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφ : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (g : ↥(H0 M Z)) :
    liftF φ (mkH M Q Z g) = φ g :=
  phi_eq_of_mkH_eq hφ (Function.invFun_eq (⟨g, rfl⟩ : ∃ a, mkH M Q Z a = mkH M Q Z g))

theorem mem_bar_H0_iff [(Q.subgroupOf M).Normal] {c : Mbar M Q} :
    c ∈ bar M Q (H0 M Z) ↔ ∃ g : ↥(H0 M Z), mkH M Q Z g = c := by
  rw [bar, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨(g : G), H0_le_M g.2⟩, Subgroup.mem_subgroupOf.mpr g.2, rfl⟩

theorem liftF_mul [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφ : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {c₁ c₂ : Mbar M Q}
    (h₁ : ∃ g : ↥(H0 M Z), mkH M Q Z g = c₁) (h₂ : ∃ g : ↥(H0 M Z), mkH M Q Z g = c₂) :
    liftF φ (c₁ * c₂) = liftF φ c₁ * liftF φ c₂ := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  have e : mkH M Q Z g₁ * mkH M Q Z g₂ = mkH M Q Z (g₁ * g₂) := (map_mul _ _ _).symm
  rw [e, liftF_mkH hφ, liftF_mkH hφ, liftF_mkH hφ, map_mul]

theorem mk_commute_iff [(Q.subgroupOf M).Normal] (x y : ↥M) :
    Commute (QuotientGroup.mk' (Q.subgroupOf M) x) (QuotientGroup.mk' (Q.subgroupOf M) y) ↔
      ⁅(x : G), (y : G)⁆ ∈ Q := by
  have h1 : Commute (QuotientGroup.mk' (Q.subgroupOf M) x)
      (QuotientGroup.mk' (Q.subgroupOf M) y) ↔
        ⁅QuotientGroup.mk' (Q.subgroupOf M) x, QuotientGroup.mk' (Q.subgroupOf M) y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.symm
  rw [h1, ← map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) x y,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

theorem comm_mem_of_mkH_mem_centralizer [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {g : ↥(H0 M Z)}
    (hg : mkH M Q Z g ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)))
    {t : G} (ht : t ∈ LB M Q B) : ⁅(g : G), t⁆ ∈ Q := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) (⟨t, htM⟩ : ↥M) ∈ bar M Q (LB M Q B) := by
    rw [bar, Subgroup.mem_map]
    exact ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hg _ hmem
  exact (mk_commute_iff (⟨(g : G), H0_le_M g.2⟩ : ↥M) ⟨t, htM⟩).mp hcomm.symm

theorem normalizer_LB_of_comm {g : G} (hL : ∀ t ∈ LB M Q B, ⁅g, t⁆ ∈ Q) :
    g ∈ Subgroup.normalizer (LB M Q B : Set G) := by
  have hQLB : Q ≤ LB M Q B := le_sup_left
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  have e : g * t * g⁻¹ = ⁅g, t⁆ * t := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (LB M Q B).mul_mem (hQLB (hL t ht)) ht

theorem stroth_sup_le_lift {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) {S : Subgroup G}
    (hSQ : S ≤ Q) : (S ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img S) := by
  refine sup_le (fun u hu => ⟨hSQ hu, M₀.pi_mem_img hu (hSQ hu)⟩) (fun z hz => ?_)
  refine ⟨h.reg.V_le hz, ?_⟩
  rw [(M₀.π_ker z (h.reg.V_le hz)).mpr hz]
  exact AddSubgroup.zero_mem _

theorem stroth_11_1b_i_aux {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (b : M₀.E) (hb0 : b ≠ 0)
    (hBline : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hodd : Odd (Nat.card K - 1)) :
    ∃ k m : ℕ, Odd m ∧
      Nat.card ↥(Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ⊓
        bar M Q (H0 M Z)) = 2 ^ k * m ∧ m ∣ Nat.card K - 1 := by
  have hlift : ∀ S : Subgroup G, S ≤ Q → (S ⊔ Z : Subgroup G) ≤ M₀.lift (M₀.img S) :=
    fun S hSQ => stroth_sup_le_lift h hSQ
  have hHM : ∀ g : ↥(H0 M Z), (g : G) ∈ M := fun g => H0_le_M g.2
  obtain ⟨g0, hg0⟩ : ∃ g0 : M₀.E, M₀.B b g0 = 1 := by
    obtain ⟨f, hf⟩ : ∃ f : M₀.E, M₀.B b f ≠ 0 := by
      by_contra hcon
      exact hb0 (M₀.nondeg b fun f => Classical.byContradiction fun hf => hcon ⟨f, hf⟩)
    exact ⟨(M₀.B b f)⁻¹ • f, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  have hBsmul : ∀ s : K, M₀.B (s • b) g0 = s := by
    intro s
    rw [map_smul, LinearMap.smul_apply, hg0, smul_eq_mul, mul_one]
  have hline : ∀ g : ↥(H0 M Z), mkH M Q Z g ∈
      Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) → ∃ s : K, φ g b = s • b := by
    intro g hg
    have hgN : (g : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      normalizer_LB_of_comm fun t ht => comm_mem_of_mkH_mem_centralizer hc hg ht
    have hgBZ := (stroth_11_1a hc hw hn (hHM g)).mpr hgN
    obtain ⟨u, huB, huQ, hu⟩ := M₀.mem_img.mp ((hBline b).mpr ⟨1, (one_smul K b).symm⟩)
    have huBZ : u ∈ (B ⊔ Z : Subgroup G) := Subgroup.mem_sup_left huB
    have hgu : (g : G) * u * (g : G)⁻¹ ∈ (B ⊔ Z : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hgBZ u).mp huBZ
    obtain ⟨s, hs⟩ := (hBline _).mp (hlift B hc.le hgu).2
    refine ⟨s, ?_⟩
    calc φ g b = φ g (M₀.π u) := by rw [hu]
      _ = M₀.π ((g : G) * u * (g : G)⁻¹) := (hφπ g u huQ).symm
      _ = s • b := hs
  obtain ⟨lamK, hlamK⟩ : ∃ lamK : Mbar M Q → K, ∀ c : Mbar M Q,
      lamK c = M₀.B (liftF φ c b) g0 := ⟨fun c => M₀.B (liftF φ c b) g0, fun c => rfl⟩
  have hscal : ∀ c : Mbar M Q, c ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) →
      c ∈ bar M Q (H0 M Z) → liftF φ c b = lamK c • b := by
    intro c hc1 hc2
    obtain ⟨g, rfl⟩ := mem_bar_H0_iff.mp hc2
    obtain ⟨s, hs⟩ := hline g hc1
    rw [liftF_mkH hφker, hs, hlamK, liftF_mkH hφker, hs, hBsmul]
  have hne : ∀ c : Mbar M Q, c ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) →
      c ∈ bar M Q (H0 M Z) → lamK c ≠ 0 := by
    intro c hc1 hc2 h0
    have h1 := hscal c hc1 hc2
    rw [h0, zero_smul] at h1
    exact hb0 ((liftF φ c).map_eq_zero_iff.mp h1)
  have hmulK : ∀ c₁ c₂ : Mbar M Q,
      c₁ ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) →
      c₁ ∈ bar M Q (H0 M Z) →
      c₂ ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) →
      c₂ ∈ bar M Q (H0 M Z) → lamK (c₁ * c₂) = lamK c₁ * lamK c₂ := by
    intro c₁ c₂ h1 h1' h2 h2'
    obtain ⟨g₁, hg₁⟩ := mem_bar_H0_iff.mp h1'
    obtain ⟨g₂, hg₂⟩ := mem_bar_H0_iff.mp h2'
    have e3 : liftF φ (c₁ * c₂) = liftF φ c₁ * liftF φ c₂ :=
      liftF_mul hφker ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
    have e4 : liftF φ (c₁ * c₂) b = (lamK c₂ * lamK c₁) • b := by
      rw [e3]
      change liftF φ c₁ (liftF φ c₂ b) = _
      rw [hscal c₂ h2 h2', map_smul, hscal c₁ h1 h1', smul_smul]
    rw [hlamK (c₁ * c₂), e4, hBsmul]
    exact mul_comm _ _
  have hkerK : ∀ c : Mbar M Q,
      c ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) →
      c ∈ bar M Q (H0 M Z) → lamK c = 1 → ∃ k : ℕ, c ^ 2 ^ k = 1 := by
    intro c hc1 hc2 h1
    obtain ⟨g, rfl⟩ := mem_bar_H0_iff.mp hc2
    have hgφ : φ g b = b := by
      have e := hscal _ hc1 hc2
      rw [liftF_mkH hφker, h1, one_smul] at e
      exact e
    have hB : ∀ u ∈ B, ⁅(g : G), u⁆ ∈ Z := by
      intro u huB
      have huQ : u ∈ Q := hc.le huB
      obtain ⟨s, hs⟩ := (hBline _).mp (M₀.pi_mem_img huB huQ)
      have hgu : (g : G) * u * (g : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hHM g)) u).mp huQ
      refine (M₀.comm_mem_iff huQ hgu).mpr ?_
      rw [hφπ g u huQ, hs, map_smul, hgφ]
    have hL : ∀ t ∈ LB M Q B, ⁅(g : G), t⁆ ∈ Q := fun t ht =>
      comm_mem_of_mkH_mem_centralizer hc hc1 ht
    obtain ⟨k, hk⟩ := stroth_11_1b_ii hc hw g.2 hL hB
    refine ⟨k, ?_⟩
    rw [← map_pow, mkH_eq_one_iff, Subgroup.coe_pow]
    exact hk
  obtain ⟨lam, hlam⟩ : ∃ lam : ↥(Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ⊓
      bar M Q (H0 M Z)) →* Kˣ, ∀ c, ((lam c : Kˣ) : K) = lamK c.1 := by
    refine ⟨MonoidHom.mk' (fun c => Units.mk0 (lamK c.1)
      (hne c.1 (Subgroup.mem_inf.mp c.2).1 (Subgroup.mem_inf.mp c.2).2)) (fun c₁ c₂ => ?_),
      fun c => rfl⟩
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, Subgroup.coe_mul]
    exact hmulK _ _ (Subgroup.mem_inf.mp c₁.2).1 (Subgroup.mem_inf.mp c₁.2).2
      (Subgroup.mem_inf.mp c₂.2).1 (Subgroup.mem_inf.mp c₂.2).2
  have hkerC : ∀ c : ↥(Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ⊓
      bar M Q (H0 M Z)), lam c = 1 → ∃ k : ℕ, c ^ 2 ^ k = 1 := by
    intro c hc1
    have h1 : lamK c.1 = 1 := by
      rw [← hlam c, hc1, Units.val_one]
    obtain ⟨k, hk⟩ := hkerK c.1 (Subgroup.mem_inf.mp c.2).1 (Subgroup.mem_inf.mp c.2).2 h1
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨k, m, hm, hcard, hdvd⟩ :=
    two_pow_mul_odd_of_hom _ lam (Nat.card K - 1) (Nat.card_units K) hodd hkerC
  exact ⟨k, m, hm, hcard, hdvd⟩

theorem stroth_11_1b_i [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) :
    ∃ k m : ℕ, Odd m ∧
      Nat.card ↥(Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ⊓
        bar M Q (H0 M Z)) = 2 ^ k * m ∧ m ∣ Nat.card Z - 1 := by
  obtain ⟨q, γ, M₀, hZq, h⟩ := stroth_globalModelDataGF hc.hyp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨b, hb0, -, hBline, -, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp h
  have hodd : Odd (Nat.card (GaloisField 2 q) - 1) := by
    rw [h.card]
    have hq0 : q ≠ 0 := by
      intro hq
      rw [hq, pow_zero] at hZq
      omega
    obtain ⟨j, hj⟩ : 2 ∣ Nat.card Z := by
      rw [hZq]
      exact dvd_pow_self 2 hq0
    exact ⟨j - 1, by omega⟩
  obtain ⟨k, m, hm, hcard, hdvd⟩ :=
    stroth_11_1b_i_aux hc hw hn h φ hφπ hφker b hb0 hBline hodd
  rw [h.card] at hdvd
  exact ⟨k, m, hm, hcard, hdvd⟩

end CFSG.RankThree.GF2n.Stroth80
