module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.Stroth.Un5ModelFacts
public import CFSG.Quasithin.Recognition.Stroth.Un5ModelProps
public import CFSG.Quasithin.Recognition.Stroth.RootGroupRegular
public import CFSG.Quasithin.Recognition.Stroth.QuadrangleKappa
public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.GH74.GLS.SP.Local.SPLRestrict

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons
  CFSG.Quasithin.H13.F431.Un CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {V : Type} {Γ : SimpleGraph V} {D : Type} [Group D] [MulAction D V]

theorem quadrangle_m_eq_two_mul_k_or_two_mul_m_eq_nine_mul_k (hA : FGQRootsAbelian)
    [Fintype V] [DecidableRel Γ.Adj] [FaithfulSMul D V] [GraphAction D Γ]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition D Γ 4)
    {k m : ℕ} (hk : 1 ≤ k) (hm : 3 ≤ m)
    (hdeg : ∀ v : V, Γ.degree v = 2 ^ m + 1 ∨ Γ.degree v = 2 ^ (3 * k) + 1)
    (hN : ∃ p : GPath Γ 4, p.NoBack ∧ Γ.degree (p 0) = 2 ^ (3 * k) + 1 ∧
      ∃ a ∈ pathRootGroup D Γ p, ∃ b ∈ pathRootGroup D Γ p, a * b ≠ b * a) :
    m = 2 * k ∨ 2 * m = 9 * k := by
  obtain ⟨p₀, hp₀, -, a₀, ha₀, b₀, hb₀, hnab₀⟩ := hN
  have hmem : ∀ (p : GPath Γ 4) (x : D), x ∈ pathRootGroup D Γ p →
      x ∈ fixingSubgroup D (Γ.neighborSet (p 1)) ⊓
        fixingSubgroup D (Γ.neighborSet (p 2)) ⊓
        fixingSubgroup D (Γ.neighborSet (p 3)) := by
    intro p x hx
    rw [mem_pathRootGroup] at hx
    simp only [Subgroup.mem_inf, mem_fixingSubgroup_iff]
    exact ⟨⟨hx 1 le_rfl (by norm_num), hx 2 (by norm_num) (by norm_num)⟩,
      hx 3 (by norm_num) (by norm_num)⟩
  by_cases hle : m ≤ 3 * k
  ·
    have hs : 1 < 2 ^ m := by
      have h1 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      norm_num at h1
      omega
    have hst : 2 ^ m ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) hle
    by_cases hpar : ∃ q' : ℕ, 2 ^ m = q' ^ 2 ∧ 2 ^ (3 * k) = q' ^ 3
    · obtain ⟨q', hq'2, hq'3⟩ := hpar
      left
      have h3 : (2 ^ k) ^ 3 = q' ^ 3 := by
        rw [← pow_mul, mul_comm]; exact hq'3
      have hq' : q' = 2 ^ k := (Nat.pow_left_injective (by norm_num : 3 ≠ 0) h3).symm
      subst hq'
      have h2 : 2 ^ m = 2 ^ (k * 2) := by rw [← pow_mul] at hq'2; exact hq'2
      have := Nat.pow_right_injective (by norm_num : 1 < 2) h2
      omega
    · refine absurd ?_ hnab₀
      have hcom := hA V Γ D hP hT hM (2 ^ m) (2 ^ (3 * k)) hs hst hdeg hpar p₀ hp₀
      exact hcom a₀ b₀ (hmem p₀ a₀ ha₀) (hmem p₀ b₀ hb₀)
  ·
    have hlt : 3 * k < m := by omega
    have hs : 1 < 2 ^ (3 * k) := by
      have h1 : 2 ^ 1 ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h1
      omega
    have hst : 2 ^ (3 * k) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hpar : ∃ q' : ℕ, 2 ^ (3 * k) = q' ^ 2 ∧ 2 ^ m = q' ^ 3
    · right
      obtain ⟨q', hq'2, hq'3⟩ := hpar
      have h6 : (2 : ℕ) ^ (9 * k) = 2 ^ (2 * m) := by
        calc 2 ^ (9 * k) = (2 ^ (3 * k)) ^ 3 := by rw [← pow_mul]; ring_nf
          _ = (q' ^ 2) ^ 3 := by rw [hq'2]
          _ = (q' ^ 3) ^ 2 := by ring
          _ = (2 ^ m) ^ 2 := by rw [hq'3]
          _ = 2 ^ (2 * m) := by rw [← pow_mul]; ring_nf
      exact Nat.pow_right_injective (by norm_num : 1 < 2) h6.symm
    · refine absurd ?_ hnab₀
      have hdeg' : ∀ v : V, Γ.degree v = 2 ^ (3 * k) + 1 ∨ Γ.degree v = 2 ^ m + 1 :=
        fun v => (hdeg v).symm
      have hcom := hA V Γ D hP hT hM (2 ^ (3 * k)) (2 ^ m) hs hst hdeg' hpar p₀ hp₀
      exact hcom a₀ b₀ (hmem p₀ a₀ ha₀) (hmem p₀ b₀ hb₀)

theorem quadrangleIdentification_of_fgq (hU : FGQHermitianUnique)
    (hA : FGQRootsAbelian) : QuadrangleIdentification := by
  intro V _ Γ _ D _ _ _ _ hP hT hM k m F _ _ _ _ hF ζ _ hk hm hdeg hex1 hex3 hN
  obtain ⟨p₀, hp₀, hdeg₀, a₀, ha₀, b₀, hb₀, hnab₀⟩ := hN
  have hq2 : 2 ≤ 2 ^ k := by
    have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
    norm_num at h ⊢
    omega
  rcases quadrangle_m_eq_two_mul_k_or_two_mul_m_eq_nine_mul_k hA hP hT hM (by omega : 1 ≤ k) hm hdeg
    ⟨p₀, hp₀, hdeg₀, a₀, ha₀, b₀, hb₀, hnab₀⟩ with hm2k | hexc
  ·
    letI : MulAction (Un5Group k F) (un5System hF ζ).Vertex := rtsMulAction _
    haveI : GraphAction (Un5Group k F) (un5System hF ζ).graph := rtsGraphAction _
    haveI : FaithfulSMul (Un5Group k F) (un5System hF ζ).Vertex := un5System_faithfulSMul hF ζ
    have hmou := rankTwoSystem_moufang (un5System hF ζ)
    have hgenM := CFSG.Quasithin.H13.F431.BN.isGenPolygon (un5System hF ζ)
    have hthickM := un5System_isThick hF ζ
    have hdegM := (un5VertexDegrees k F hF ζ).1
    have hex1M := (un5VertexDegrees k F hF ζ).2.1
    have hex3M := (un5VertexDegrees k F hF ζ).2.2
    have hdegΓ : ∀ v : V, Γ.degree v = (2 ^ k) ^ 2 + 1 ∨ Γ.degree v = (2 ^ k) ^ 3 + 1 := by
      intro v
      rcases hdeg v with h | h
      · left
        calc Γ.degree v = 2 ^ m + 1 := h
          _ = 2 ^ (k * 2) + 1 := by rw [hm2k, mul_comm]
          _ = (2 ^ k) ^ 2 + 1 := by rw [pow_mul]
      · right
        calc Γ.degree v = 2 ^ (3 * k) + 1 := h
          _ = 2 ^ (k * 3) + 1 := by rw [mul_comm 3 k]
          _ = (2 ^ k) ^ 3 + 1 := by rw [pow_mul]
    have hex1Γ : ∃ v : V, Γ.degree v = (2 ^ k) ^ 2 + 1 := by
      obtain ⟨v, hv⟩ := hex1
      exact ⟨v, by rw [hv, hm2k, mul_comm, pow_mul]⟩
    have hex3Γ : ∃ v : V, Γ.degree v = (2 ^ k) ^ 3 + 1 := by
      obtain ⟨v, hv⟩ := hex3
      exact ⟨v, by rw [hv, mul_comm 3 k, pow_mul]⟩
    obtain ⟨φ, hφdeg⟩ := hU (2 ^ k) V (un5System hF ζ).Vertex Γ (un5System hF ζ).graph D
      (Un5Group k F) hq2 hP hT (isGeneralizedPolygon_of_isGenPolygon (by norm_num) hgenM)
      hthickM hM hmou hdegΓ hdegM hex1Γ hex3Γ hex1M hex3M
    refine ⟨hm2k, φ, un5Kappa hF ζ hP hT hM φ, fun g v => ?_⟩
    exact un5Kappa_equivariant hF ζ hP hT hM φ g v
  ·
    have h2k : 2 ∣ k := by
      have h2 : 2 ∣ 9 * k := by rw [← hexc]; exact ⟨m, rfl⟩
      exact ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 2)).mp h2).resolve_left (by norm_num)
    obtain ⟨j, rfl⟩ := h2k
    have hmj : m = 9 * j := by omega
    have hj1 : 1 ≤ j := by omega
    have hq2' : 2 ≤ 2 ^ (3 * j) := by
      have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ 3 * j)
      norm_num at h ⊢
      omega
    let F' := GaloisField 2 (6 * j)
    have hF' : Nat.card F' = (2 ^ (3 * j)) ^ 2 := by
      rw [GaloisField.card 2 (6 * j) (by omega), show 6 * j = 3 * j * 2 by ring, pow_mul]
    obtain ⟨ζ', hζ'⟩ := exists_traceZero_ne_zero (p := 2) (f := 3 * j) hF'
    haveI : Fact ((ζ' : F') ≠ 0) := ⟨hζ'⟩
    letI : MulAction (Un5Group (3 * j) F') (un5System hF' ζ').Vertex := rtsMulAction _
    haveI : GraphAction (Un5Group (3 * j) F') (un5System hF' ζ').graph := rtsGraphAction _
    haveI : FaithfulSMul (Un5Group (3 * j) F') (un5System hF' ζ').Vertex :=
      un5System_faithfulSMul hF' ζ'
    have hmou' := rankTwoSystem_moufang (un5System hF' ζ')
    have hgenM' := CFSG.Quasithin.H13.F431.BN.isGenPolygon (un5System hF' ζ')
    have hthickM' := un5System_isThick hF' ζ'
    have hdegM' := (un5VertexDegrees (3 * j) F' hF' ζ').1
    have hex1M' := (un5VertexDegrees (3 * j) F' hF' ζ').2.1
    have hex3M' := (un5VertexDegrees (3 * j) F' hF' ζ').2.2
    have hdegΓ : ∀ v : V, Γ.degree v = (2 ^ (3 * j)) ^ 2 + 1 ∨
        Γ.degree v = (2 ^ (3 * j)) ^ 3 + 1 := by
      intro v
      rcases hdeg v with h | h
      · right
        calc Γ.degree v = 2 ^ m + 1 := h
          _ = 2 ^ (9 * j) + 1 := by rw [hmj]
          _ = (2 ^ (3 * j)) ^ 3 + 1 := by
            rw [show 9 * j = 3 * j * 3 by ring, pow_mul]
      · left
        calc Γ.degree v = 2 ^ (3 * (2 * j)) + 1 := h
          _ = 2 ^ (6 * j) + 1 := by rw [show 3 * (2 * j) = 6 * j by ring]
          _ = (2 ^ (3 * j)) ^ 2 + 1 := by
            rw [show 6 * j = 3 * j * 2 by ring, pow_mul]
    have hsqΓ : ∃ v : V, Γ.degree v = (2 ^ (3 * j)) ^ 2 + 1 := by
      obtain ⟨v, hv⟩ := hex3
      refine ⟨v, ?_⟩
      rw [hv, show 3 * (2 * j) = 6 * j by ring, show 6 * j = 3 * j * 2 by ring, pow_mul]
    have hcubeΓ : ∃ v : V, Γ.degree v = (2 ^ (3 * j)) ^ 3 + 1 := by
      obtain ⟨v, hv⟩ := hex1
      refine ⟨v, ?_⟩
      rw [hv, hmj, show 9 * j = 3 * j * 3 by ring, pow_mul]
    obtain ⟨φ, hφdeg⟩ := hU (2 ^ (3 * j)) V (un5System hF' ζ').Vertex Γ (un5System hF' ζ').graph
      D (Un5Group (3 * j) F') hq2' hP hT
      (isGeneralizedPolygon_of_isGenPolygon (by norm_num) hgenM') hthickM' hM hmou' hdegΓ hdegM'
      hsqΓ hcubeΓ hex1M' hex3M'
    have hφadj : ∀ a b, Γ.Adj a b → (un5System hF' ζ').graph.Adj (φ a) (φ b) :=
      fun a b h => φ.map_adj_iff.mpr h
    let q : GPath (un5System hF' ζ').graph 4 := p₀.map φ hφadj
    have hq : q.NoBack := GPath.NoBack.map_of_injective hφadj φ.toEquiv.injective hp₀
    have hq0 : q 0 = φ (p₀ 0) := rfl
    have hdegq : (un5System hF' ζ').graph.degree (q 0) = (2 ^ (3 * j)) ^ 2 + 1 := by
      rw [hq0, hφdeg (p₀ 0), hdeg₀, show 3 * (2 * j) = 6 * j by ring,
        show 6 * j = 3 * j * 2 by ring, pow_mul]
    obtain ⟨ha, hha, hha'⟩ := exists_rootGroup_map (Γ := Γ) (Δ := (un5System hF' ζ').graph)
      (D := D) (H := Un5Group (3 * j) F') hT hgenM'
      (three_le_encard_of_isThick hthickM') hmou' φ hp₀ ha₀
    obtain ⟨hb, hhb, hhb'⟩ := exists_rootGroup_map (Γ := Γ) (Δ := (un5System hF' ζ').graph)
      (D := D) (H := Un5Group (3 * j) F') hT hgenM'
      (three_le_encard_of_isThick hthickM') hmou' φ hp₀ hb₀
    have hcomm : ha * hb = hb * ha :=
      un5ShortRootGroupsAbelian (3 * j) F' hF' ζ' q hq hdegq ha hb hha hhb
    have hha'' : ∀ x : V, φ.toEquiv (a₀ • x) = ha • φ.toEquiv x := fun x => hha' x
    have hhb'' : ∀ x : V, φ.toEquiv (b₀ • x) = hb • φ.toEquiv x := fun x => hhb' x
    have hab : a₀ * b₀ = b₀ * a₀ := by
      refine FaithfulSMul.eq_of_smul_eq_smul (α := V) (m₁ := a₀ * b₀) (m₂ := b₀ * a₀)
        (fun x => ?_)
      refine φ.toEquiv.injective ?_
      calc φ.toEquiv ((a₀ * b₀) • x) = φ.toEquiv (a₀ • (b₀ • x)) := by rw [mul_smul]
        _ = ha • φ.toEquiv (b₀ • x) := hha'' (b₀ • x)
        _ = ha • (hb • φ.toEquiv x) := by rw [hhb'' x]
        _ = (ha * hb) • φ.toEquiv x := by rw [mul_smul]
        _ = (hb * ha) • φ.toEquiv x := by rw [hcomm]
        _ = hb • (ha • φ.toEquiv x) := by rw [mul_smul]
        _ = hb • φ.toEquiv (a₀ • x) := by rw [hha'' x]
        _ = φ.toEquiv (b₀ • (a₀ • x)) := (hhb'' (a₀ • x)).symm
        _ = φ.toEquiv ((b₀ * a₀) • x) := by rw [mul_smul]
    exact (hnab₀ hab).elim

end CFSG.Quasithin.Stroth