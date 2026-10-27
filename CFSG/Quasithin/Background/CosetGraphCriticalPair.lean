module

public import CFSG.Quasithin.Background.CosetGraphCritical

public section

namespace CFSG.Quasithin.CosetGraph

variable {G : Type*} [Group G] {A B : Subgroup G}

@[expose] def kerA (A B : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ A ∧ ∀ a ∈ A, a⁻¹ * z * a ∈ B}
  mul_mem' := by
    rintro x y ⟨hxA, hx⟩ ⟨hyA, hy⟩
    refine ⟨A.mul_mem hxA hyA, fun a ha => ?_⟩
    have : a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
    rw [this]
    exact B.mul_mem (hx a ha) (hy a ha)
  one_mem' := ⟨A.one_mem, fun a ha => by simpa using B.one_mem⟩
  inv_mem' := by
    rintro x ⟨hxA, hx⟩
    refine ⟨A.inv_mem hxA, fun a ha => ?_⟩
    have : a⁻¹ * x⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by group
    rw [this]
    exact B.inv_mem (hx a ha)

@[expose] def kerB (A B : Subgroup G) : Subgroup G := kerA B A

private theorem smul_alphaV_eq (x : G) : x • alphaV A B = .inl ((x : G) : G ⧸ A) := by
  show Sum.inl ((x * 1 : G) : G ⧸ A) = _
  rw [mul_one]

private theorem smul_betaV_eq (x : G) : x • betaV A B = .inr ((x : G) : G ⧸ B) := by
  show Sum.inr ((x * 1 : G) : G ⧸ B) = _
  rw [mul_one]

private theorem mem_kerA {z : G} : z ∈ kerA A B ↔ z ∈ A ∧ ∀ a ∈ A, a⁻¹ * z * a ∈ B := Iff.rfl

theorem mem_stabilizer_smul_alphaV (x g : G) :
    g ∈ MulAction.stabilizer G (x • alphaV A B) ↔ x⁻¹ * g * x ∈ A := by
  rw [← mem_stabilizer_alphaV (A := A) (B := B) (x⁻¹ * g * x), MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · intro h
    have e : x * (x⁻¹ * g * x) = g * x := by group
    calc g • x • alphaV A B = (g * x) • alphaV A B := by rw [mul_smul]
      _ = (x * (x⁻¹ * g * x)) • alphaV A B := by rw [e]
      _ = x • ((x⁻¹ * g * x) • alphaV A B) := by rw [smul_smul]
      _ = x • alphaV A B := by rw [h]

theorem mem_stabilizer_smul_betaV (x g : G) :
    g ∈ MulAction.stabilizer G (x • betaV A B) ↔ x⁻¹ * g * x ∈ B := by
  rw [← mem_stabilizer_betaV (A := A) (B := B) (x⁻¹ * g * x), MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · intro h
    have e : x * (x⁻¹ * g * x) = g * x := by group
    calc g • x • betaV A B = (g * x) • betaV A B := by rw [mul_smul]
      _ = (x * (x⁻¹ * g * x)) • betaV A B := by rw [e]
      _ = x • ((x⁻¹ * g * x) • betaV A B) := by rw [smul_smul]
      _ = x • betaV A B := by rw [h]

theorem exists_eq_smul_betaV_of_adj {x : G} {w : (G ⧸ A) ⊕ (G ⧸ B)}
    (h : (amalgamGraph A B).Adj w (x • alphaV A B)) : ∃ a ∈ A, w = (x * a) • betaV A B := by
  rw [amalgamGraph_adj_iff, smul_alphaV_eq] at h
  rcases h with ⟨g, rfl, hg⟩ | ⟨g, hg, rfl⟩
  · cases hg
  · have hxg : ((x : G) : G ⧸ A) = ((g : G) : G ⧸ A) := Sum.inl.inj hg
    have ha : x⁻¹ * g ∈ A := QuotientGroup.eq.mp hxg
    refine ⟨x⁻¹ * g, ha, ?_⟩
    rw [smul_betaV_eq, mul_inv_cancel_left]

theorem exists_eq_smul_alphaV_of_adj {y : G} {w : (G ⧸ A) ⊕ (G ⧸ B)}
    (h : (amalgamGraph A B).Adj w (y • betaV A B)) : ∃ b ∈ B, w = (y * b) • alphaV A B := by
  rw [amalgamGraph_adj_iff, smul_betaV_eq] at h
  rcases h with ⟨g, rfl, hg⟩ | ⟨g, hg, rfl⟩
  · have hyg : ((y : G) : G ⧸ B) = ((g : G) : G ⧸ B) := Sum.inr.inj hg
    have hb : y⁻¹ * g ∈ B := QuotientGroup.eq.mp hyg
    refine ⟨y⁻¹ * g, hb, ?_⟩
    rw [smul_alphaV_eq, mul_inv_cancel_left]
  · cases hg

theorem mem_kernelAt_smul_alphaV (x z : G) :
    z ∈ kernelAt (amalgamGraph A B) (x • alphaV A B) ↔ x⁻¹ * z * x ∈ kerA A B := by
  have hnb : ∀ a ∈ A, (amalgamGraph A B).Adj (x • alphaV A B) ((x * a) • betaV A B) := by
    intro a ha
    refine (amalgamGraph_adj_iff _ _).mpr (Or.inl ⟨x * a, ?_, smul_betaV_eq _⟩)
    rw [smul_alphaV_eq, Sum.inl.injEq, QuotientGroup.eq, inv_mul_cancel_left]
    exact ha
  rw [mem_kerA]
  simp only [kernelAt, Subgroup.mem_inf, Subgroup.mem_iInf, SimpleGraph.mem_neighborSet]
  rw [mem_stabilizer_smul_alphaV]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a ha => ?_⟩
    have h3 := h2 _ (hnb a ha)
    rw [mem_stabilizer_smul_betaV] at h3
    have e : (x * a)⁻¹ * z * (x * a) = a⁻¹ * (x⁻¹ * z * x) * a := by group
    rw [e] at h3
    exact h3
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun w hw => ?_⟩
    obtain ⟨a, ha, rfl⟩ := exists_eq_smul_betaV_of_adj hw.symm
    rw [mem_stabilizer_smul_betaV]
    have e : (x * a)⁻¹ * z * (x * a) = a⁻¹ * (x⁻¹ * z * x) * a := by group
    rw [e]
    exact h2 a ha

theorem mem_kernelAt_smul_betaV (x z : G) :
    z ∈ kernelAt (amalgamGraph A B) (x • betaV A B) ↔ x⁻¹ * z * x ∈ kerB A B := by
  have hnb : ∀ b ∈ B, (amalgamGraph A B).Adj (x • betaV A B) ((x * b) • alphaV A B) := by
    intro b hb
    refine (amalgamGraph_adj_iff _ _).mpr (Or.inr ⟨x * b, smul_alphaV_eq _, ?_⟩)
    rw [smul_betaV_eq, Sum.inr.injEq, QuotientGroup.eq, inv_mul_cancel_left]
    exact hb
  rw [kerB, mem_kerA]
  simp only [kernelAt, Subgroup.mem_inf, Subgroup.mem_iInf, SimpleGraph.mem_neighborSet]
  rw [mem_stabilizer_smul_betaV]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun b hb => ?_⟩
    have h3 := h2 _ (hnb b hb)
    rw [mem_stabilizer_smul_alphaV] at h3
    have e : (x * b)⁻¹ * z * (x * b) = b⁻¹ * (x⁻¹ * z * x) * b := by group
    rw [e] at h3
    exact h3
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun w hw => ?_⟩
    obtain ⟨b, hb, rfl⟩ := exists_eq_smul_alphaV_of_adj hw.symm
    rw [mem_stabilizer_smul_alphaV]
    have e : (x * b)⁻¹ * z * (x * b) = b⁻¹ * (x⁻¹ * z * x) * b := by group
    rw [e]
    exact h2 b hb

theorem kerB_eq_inf (hB : B ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G)) :
    kerB A B = A ⊓ B := by
  ext z
  rw [kerB, mem_kerA, Subgroup.mem_inf]
  constructor
  · rintro ⟨hzB, h⟩
    refine ⟨?_, hzB⟩
    simpa using h 1 B.one_mem
  · rintro ⟨hzA, hzB⟩
    refine ⟨hzB, fun b hb => ?_⟩
    have hmem : b⁻¹ * z * b ∈ ((A ⊓ B : Subgroup G) : Set G) := by
      refine (Subgroup.mem_normalizer_iff.mp (hB hb) (b⁻¹ * z * b)).mpr ?_
      have e : b * (b⁻¹ * z * b) * b⁻¹ = z := by group
      rw [e]
      exact SetLike.mem_coe.mpr (Subgroup.mem_inf.mpr ⟨hzA, hzB⟩)
    exact (Subgroup.mem_inf.mp (SetLike.mem_coe.mp hmem)).1

private theorem mem_of_walk_of_closed {V : Type*} {Γ : SimpleGraph V} (P : V → Prop)
    (hP : ∀ w, P w → ∀ v, Γ.Adj w v → P v) {u v : V} (p : Γ.Walk u v) : P u → P v := by
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (hP _ hu _ h)

theorem exists_eq_smul_of_reachable {v : (G ⧸ A) ⊕ (G ⧸ B)}
    (hv : (amalgamGraph A B).Reachable (alphaV A B) v) :
    ∃ x ∈ A ⊔ B, v = x • alphaV A B ∨ v = x • betaV A B := by
  have hAX : A ≤ A ⊔ B := le_sup_left
  have hBX : B ≤ A ⊔ B := le_sup_right
  obtain ⟨p⟩ := hv
  refine mem_of_walk_of_closed
    (fun v => ∃ x ∈ A ⊔ B, v = x • alphaV A B ∨ v = x • betaV A B) ?_ p ?_
  · rintro w ⟨x, hx, rfl | rfl⟩ v hadj
    · obtain ⟨a, ha, rfl⟩ := exists_eq_smul_betaV_of_adj hadj.symm
      exact ⟨x * a, (A ⊔ B).mul_mem hx (hAX ha), Or.inr rfl⟩
    · obtain ⟨b, hb, rfl⟩ := exists_eq_smul_alphaV_of_adj hadj.symm
      exact ⟨x * b, (A ⊔ B).mul_mem hx (hBX hb), Or.inl rfl⟩
  · exact ⟨1, (A ⊔ B).one_mem, Or.inl (by rw [one_smul])⟩

private theorem exists_walk_penultimate {V : Type*} {Γ : SimpleGraph V} {δ ε : V}
    (p : Γ.Walk δ ε) : p.length ≠ 0 →
      ∃ ε₁, Γ.Adj ε₁ ε ∧ ∃ q : Γ.Walk δ ε₁, q.length + 1 = p.length := by
  induction p with
  | nil => intro hp; simp at hp
  | @cons a b c hab p' ih =>
    intro _
    by_cases h0 : p'.length = 0
    · obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero h0
      exact ⟨a, hab, SimpleGraph.Walk.nil, by simp [h0]⟩
    · obtain ⟨ε₁, hadj, q, hq⟩ := ih h0
      exact ⟨ε₁, hadj, SimpleGraph.Walk.cons hab q,
        by simp only [SimpleGraph.Walk.length_cons]; omega⟩

theorem exists_adj_dist_eq_pred {V : Type*} (Γ : SimpleGraph V) {δ ε : V}
    (h : Γ.Reachable δ ε) (hb : Γ.dist δ ε ≠ 0) :
    ∃ ε₁, Γ.Adj ε₁ ε ∧ Γ.dist δ ε₁ + 1 = Γ.dist δ ε := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  obtain ⟨ε₁, hadj, q, hq⟩ := exists_walk_penultimate p (by rwa [hp])
  refine ⟨ε₁, hadj, ?_⟩
  have h1 : Γ.dist δ ε₁ ≤ q.length := SimpleGraph.dist_le q
  have hr : Γ.Reachable δ ε₁ := ⟨q⟩
  obtain ⟨q', hq'⟩ := hr.exists_walk_length_eq_dist
  have h2 : Γ.dist δ ε ≤ Γ.dist δ ε₁ + 1 := by
    have key := SimpleGraph.dist_le (q'.concat hadj)
    rw [SimpleGraph.Walk.length_concat, hq'] at key
    exact key
  omega

theorem zAt_smul_alphaV {U : Subgroup G} (hAU : A ≤ Subgroup.normalizer (U : Set G)) (x : G) :
    zAt A B U (x • alphaV A B) = U.map (MulAut.conj x).toMonoidHom := by
  rw [smul_alphaV_eq]
  change U.map (MulAut.conj (Quotient.out (x : G ⧸ A))).toMonoidHom = _
  have hout : ((Quotient.out (x : G ⧸ A) : G) : G ⧸ A) = (x : G ⧸ A) :=
    QuotientGroup.out_eq' _
  have hd : x⁻¹ * Quotient.out (x : G ⧸ A) ∈ A := by
    have h2 := A.inv_mem (QuotientGroup.eq.mp hout)
    simpa using h2
  obtain ⟨d, hd', hgd⟩ : ∃ d ∈ A, Quotient.out (x : G ⧸ A) = x * d :=
    ⟨x⁻¹ * Quotient.out (x : G ⧸ A), hd, (mul_inv_cancel_left _ _).symm⟩
  rw [hgd]
  have hcomp : (MulAut.conj (x * d)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj d).toMonoidHom := by
    ext y
    simp [mul_assoc]
  have hdU : U.map (MulAut.conj d).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAU hd')
  rw [hcomp, ← Subgroup.map_map, hdU]

theorem kernelAt_le_of_adj_smul_betaV
    (hB : B ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G)) {y : G}
    {w : (G ⧸ A) ⊕ (G ⧸ B)} (h : (amalgamGraph A B).Adj w (y • betaV A B)) :
    kernelAt (G := G) (amalgamGraph A B) w ≤ kernelAt (G := G) (amalgamGraph A B) (y • betaV A B) := by
  obtain ⟨b, hb, rfl⟩ := exists_eq_smul_alphaV_of_adj h
  intro z hz
  rw [mem_kernelAt_smul_alphaV] at hz
  rw [mem_kernelAt_smul_betaV, kerB_eq_inf hB]
  have hz' : (y * b)⁻¹ * z * (y * b) ∈ A ⊓ B := by
    rw [mem_kerA] at hz
    exact Subgroup.mem_inf.mpr ⟨hz.1, by simpa using hz.2 1 A.one_mem⟩
  have hm := (Subgroup.mem_normalizer_iff.mp (hB hb) ((y * b)⁻¹ * z * (y * b))).mp
    (SetLike.mem_coe.mpr hz')
  have e : b * ((y * b)⁻¹ * z * (y * b)) * b⁻¹ = y⁻¹ * z * y := by group
  rw [e] at hm
  exact SetLike.mem_coe.mp hm

@[expose] def typeOneG (A B : Subgroup G) : (G ⧸ A) ⊕ (G ⧸ B) → Prop :=
  fun v => v.isLeft ∧ (amalgamGraph A B).Reachable (alphaV A B) v

theorem exists_conj_of_isCriticalPair {U : Subgroup G}
    (hBR : B ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G))
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hUk : U ≤ kerA A B)
    {δ ε : (G ⧸ A) ⊕ (G ⧸ B)}
    (hc : IsCriticalPair (amalgamGraph A B) (zAt A B U) (typeOneG A B) δ ε) :
    ∃ g ∈ A ⊔ B, (∀ u ∈ U, g⁻¹ * u * g ∈ A ⊓ B) ∧ (∀ u ∈ U, g * u * g⁻¹ ∈ A ⊓ B) ∧
      ∃ u ∈ U, g⁻¹ * u * g ∉ kerA A B := by
  classical
  obtain ⟨hPδ, hδε, hnk, hmin⟩ := hc
  have hAX : A ≤ A ⊔ B := le_sup_left
  obtain ⟨x, hxX, hδ⟩ : ∃ x ∈ A ⊔ B, δ = x • alphaV A B := by
    obtain ⟨x, hx, h | h⟩ := exists_eq_smul_of_reachable hPδ.2
    · exact ⟨x, hx, h⟩
    · exfalso
      have := hPδ.1
      rw [h] at this
      simp [betaV] at this
  have hεα : (amalgamGraph A B).Reachable (alphaV A B) ε := hPδ.2.trans hδε
  subst hδ
  have hUA : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun a ha u hu =>
    (Subgroup.mem_normalizer_iff.mp (hAU ha) u).mp hu
  have hUA' : ∀ a ∈ A, ∀ u ∈ U, a⁻¹ * u * a ∈ U := fun a ha u hu => by
    simpa using hUA a⁻¹ (A.inv_mem ha) u hu
  have hZ : ∀ y : G, zAt A B U (y • alphaV A B) = U.map (MulAut.conj y).toMonoidHom :=
    zAt_smul_alphaV hAU
  have hmemZ : ∀ (y z : G), z ∈ zAt A B U (y • alphaV A B) ↔ ∃ u ∈ U, y * u * y⁻¹ = z := by
    intro y z
    rw [hZ y]
    simp [Subgroup.mem_map]
  have hb : (amalgamGraph A B).dist (x • alphaV A B) ε ≠ 0 := by
    intro h0
    have heq : x • alphaV A B = ε := by
      rcases (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable).mp h0 with h | h
      · exact h
      · exact absurd hδε h
    apply hnk
    rw [← heq]
    intro z hz
    obtain ⟨u, hu, rfl⟩ := (hmemZ x z).mp hz
    rw [mem_kernelAt_smul_alphaV]
    have : x⁻¹ * (x * u * x⁻¹) * x = u := by group
    rw [this]
    exact hUk hu
  obtain ⟨ε₁, hε₁adj, hε₁d⟩ := exists_adj_dist_eq_pred (amalgamGraph A B) hδε hb
  have hδε₁ : (amalgamGraph A B).Reachable (x • alphaV A B) ε₁ :=
    hδε.trans hε₁adj.symm.reachable
  have hZε₁ : zAt A B U (x • alphaV A B) ≤ kernelAt (amalgamGraph A B) ε₁ :=
    hmin (x • alphaV A B) ε₁ hPδ hδε₁ (by omega)
  have hεL : ε.isLeft = true := by
    by_contra hεL
    obtain ⟨y, hy, h | h⟩ := exists_eq_smul_of_reachable hεα
    · rw [h] at hεL
      simp [alphaV] at hεL
    · rw [h] at hε₁adj hnk
      exact hnk (hZε₁.trans (kernelAt_le_of_adj_smul_betaV hBR hε₁adj))
  obtain ⟨g', hg'X, hg'⟩ : ∃ g' ∈ A ⊔ B, ε = g' • alphaV A B := by
    obtain ⟨y, hy, h | h⟩ := exists_eq_smul_of_reachable hεα
    · exact ⟨y, hy, h⟩
    · exfalso
      rw [h] at hεL
      simp [betaV] at hεL
  have hb' : (amalgamGraph A B).dist ε (x • alphaV A B) ≠ 0 := by
    rwa [SimpleGraph.dist_comm]
  obtain ⟨δ₁, hδ₁adj, hδ₁d⟩ := exists_adj_dist_eq_pred (amalgamGraph A B) hδε.symm hb'
  have hPε : typeOneG A B ε := ⟨hεL, hεα⟩
  have hεδ₁ : (amalgamGraph A B).Reachable ε δ₁ := hδε.symm.trans hδ₁adj.symm.reachable
  have hZδ₁ : zAt A B U ε ≤ kernelAt (amalgamGraph A B) δ₁ :=
    hmin ε δ₁ hPε hεδ₁ (by
      have hc : (amalgamGraph A B).dist ε (x • alphaV A B) =
          (amalgamGraph A B).dist (x • alphaV A B) ε := SimpleGraph.dist_comm
      omega)
  rw [hg'] at hε₁adj hnk hZδ₁
  obtain ⟨a, ha, hε₁⟩ := exists_eq_smul_betaV_of_adj hε₁adj
  obtain ⟨a₁, ha₁, hδ₁⟩ := exists_eq_smul_betaV_of_adj hδ₁adj
  rw [hε₁] at hZε₁
  rw [hδ₁] at hZδ₁
  have hgα : (g' * a) • alphaV A B = g' • alphaV A B := by
    rw [mul_smul]
    congr 1
    exact (MulAction.mem_stabilizer_iff).mp ((mem_stabilizer_alphaV a).mpr ha)
  have hxα : (x * a₁) • alphaV A B = x • alphaV A B := by
    rw [mul_smul]
    congr 1
    exact (MulAction.mem_stabilizer_iff).mp ((mem_stabilizer_alphaV a₁).mpr ha₁)
  have hkB := kerB_eq_inf hBR
  refine ⟨(x * a₁)⁻¹ * (g' * a), ?_, ?_, ?_, ?_⟩
  · exact (A ⊔ B).mul_mem ((A ⊔ B).inv_mem ((A ⊔ B).mul_mem hxX (hAX ha₁)))
      ((A ⊔ B).mul_mem hg'X (hAX ha))
  · intro u hu
    have hz : x * (a₁ * u * a₁⁻¹) * x⁻¹ ∈ zAt A B U (x • alphaV A B) :=
      (hmemZ x _).mpr ⟨_, hUA a₁ ha₁ u hu, rfl⟩
    have h1 := (mem_kernelAt_smul_betaV (A := A) (B := B) (g' * a) _).mp (hZε₁ hz)
    rw [hkB] at h1
    have e : ((x * a₁)⁻¹ * (g' * a))⁻¹ * u * ((x * a₁)⁻¹ * (g' * a)) =
        (g' * a)⁻¹ * (x * (a₁ * u * a₁⁻¹) * x⁻¹) * (g' * a) := by group
    rw [e]
    exact h1
  · intro u hu
    have hz : g' * (a * u * a⁻¹) * g'⁻¹ ∈ zAt A B U (g' • alphaV A B) :=
      (hmemZ g' _).mpr ⟨_, hUA a ha u hu, rfl⟩
    have h1 := (mem_kernelAt_smul_betaV (A := A) (B := B) (x * a₁) _).mp (hZδ₁ hz)
    rw [hkB] at h1
    have e : ((x * a₁)⁻¹ * (g' * a)) * u * ((x * a₁)⁻¹ * (g' * a))⁻¹ =
        (x * a₁)⁻¹ * (g' * (a * u * a⁻¹) * g'⁻¹) * (x * a₁) := by group
    rw [e]
    exact h1
  · rw [← hgα] at hnk
    by_contra hcon
    push Not at hcon
    apply hnk
    intro z hz
    obtain ⟨u₀, hu₀, rfl⟩ := (hmemZ x z).mp hz
    rw [mem_kernelAt_smul_alphaV]
    have e : (g' * a)⁻¹ * (x * u₀ * x⁻¹) * (g' * a) =
        ((x * a₁)⁻¹ * (g' * a))⁻¹ * (a₁⁻¹ * u₀ * a₁) * ((x * a₁)⁻¹ * (g' * a)) := by group
    rw [e]
    exact hcon _ (hUA' a₁ ha₁ u₀ hu₀)

end CFSG.Quasithin.CosetGraph
