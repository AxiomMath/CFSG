module

public import CFSG.LocalAnalysis.WeakClosure81.EightFourteen
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationCounting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

section Sit

variable {V H T A L K : Subgroup G} {i : ℕ}

theorem Sit813.oTwoMod_le_centralizer_uGrp (h : Sit813 V H T i A L K)
    (hNV : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G)) :
    oTwoMod (cGrp H T) K ≤ centralizer (uGrp V K : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h.commute_oTwoMod_uGrp hNV hn hu).symm

theorem Sit813.conj_mul_conj_of_comm_mem_oTwoMod (h : Sit813 V H T i A L K)
    (hNV : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G)) {c : G}
    (hcV : c ∈ normalizer (V : Set G)) (hcK : c ∈ normalizer (K : Set G))
    (hc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K) {k u : G} (hk : k ∈ K)
    (hu : u ∈ uGrp V K) : c * (k * u * k⁻¹) * c⁻¹ = k * (c * u * c⁻¹) * k⁻¹ := by
  have hcU : c ∈ normalizer (uGrp V K : Set G) :=
    mem_normalizer_conjClosure_of_mem_normalizers hcV hcK
  have hu' : c * u * c⁻¹ ∈ uGrp V K := (Subgroup.mem_normalizer_iff.mp hcU u).mp hu
  have hw : k * (c * u * c⁻¹) * k⁻¹ ∈ uGrp V K :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V K hk) _).mp hu'
  have hcomm := h.commute_oTwoMod_uGrp hNV (hc k hk) hw
  calc c * (k * u * k⁻¹) * c⁻¹
      = (c * k * c⁻¹ * k⁻¹) * (k * (c * u * c⁻¹) * k⁻¹) * (c * k * c⁻¹ * k⁻¹)⁻¹ := by group
    _ = k * (c * u * c⁻¹) * k⁻¹ := by rw [hcomm]; group

theorem Sit813.exists_comm_not_mem_u1Grp_inf_centralizer (h : Sit813 V H T i A L K) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) :
    ∃ k ∈ K, k * v * k⁻¹ * v⁻¹ ∉ u1Grp V H T A K ⊓ centralizer (K : Set G) := by
  by_contra hcon
  push Not at hcon
  have hBK : K ⊓ centralizer ({v} : Set G) ≤ K := inf_le_left
  have key : ∀ g ∈ K, ∀ b ∈ K ⊓ centralizer ({v} : Set G),
      g * b * g⁻¹ ∈ K ⊓ centralizer ({v} : Set G) := by
    intro g hg b hb
    obtain ⟨hbK, hbv⟩ := Subgroup.mem_inf.mp hb
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hg hbK) (K.inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hd := (Subgroup.mem_inf.mp (hcon g⁻¹ (K.inv_mem hg))).2
    have hd' := Subgroup.mem_centralizer_iff.mp hd b hbK
    simp only [inv_inv] at hd'
    have hbv' : b * v = v * b :=
      (Subgroup.mem_centralizer_iff.mp hbv v (Set.mem_singleton v)).symm
    have hbw : b * (g⁻¹ * v * g) = (g⁻¹ * v * g) * b := by
      calc b * (g⁻¹ * v * g) = (b * (g⁻¹ * v * g * v⁻¹)) * v := by group
        _ = ((g⁻¹ * v * g * v⁻¹) * b) * v := by rw [hd']
        _ = (g⁻¹ * v * g * v⁻¹) * (b * v) := by group
        _ = (g⁻¹ * v * g * v⁻¹) * (v * b) := by rw [hbv']
        _ = (g⁻¹ * v * g) * b := by group
    calc v * (g * b * g⁻¹) = g * ((g⁻¹ * v * g) * b) * g⁻¹ := by group
      _ = g * (b * (g⁻¹ * v * g)) * g⁻¹ := by rw [hbw]
      _ = (g * b * g⁻¹) * v := by group
  have hBnorm : ((K ⊓ centralizer ({v} : Set G)).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBK]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro b
    exact ⟨key g hg b, fun hb => by simpa [mul_assoc] using key g⁻¹ (K.inv_mem hg) _ hb⟩
  have hKMB : K ⊓ normalizer (V : Set G) ≤ K ⊓ centralizer ({v} : Set G) := by
    intro p hp
    obtain ⟨hpK, hpV⟩ := Subgroup.mem_inf.mp hp
    refine Subgroup.mem_inf.mpr ⟨hpK, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hdV : p * v * p⁻¹ * v⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp hpV v).mp hv) (V.inv_mem hv)
    have hdC := (Subgroup.mem_inf.mp (hcon p hpK)).2
    have h1 : p * v * p⁻¹ * v⁻¹ = 1 :=
      h.eq_one_of_centralizes_K hdV fun k hk => Subgroup.mem_centralizer_iff.mp hdC k hk
    calc v * p = (p * v * p⁻¹ * v⁻¹)⁻¹ * (p * v) := by group
      _ = p * v := by rw [h1]; group
  have hNB : oTwoMod (cGrp H T) K ≤ K ⊓ centralizer ({v} : Set G) :=
    h.oTwoMod_le_inf.trans hKMB
  rcases h.kn1 _ hNB hBK hBnorm with h1 | h1
  · have heq : K ⊓ normalizer (V : Set G) = oTwoMod (cGrp H T) K :=
      le_antisymm (hKMB.trans h1.le) h.oTwoMod_le_inf
    have h5 := h.concl813.d_index
    rw [heq, h.kn4] at h5
    omega
  · refine hv1 (h.eq_one_of_centralizes_K hv fun k hk => ?_)
    have hk' : k ∈ K ⊓ centralizer ({v} : Set G) := by rw [h1]; exact hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk').2 v (Set.mem_singleton v)).symm

theorem Sit813.centralizes_V_of_comm_mem_oTwoMod (h : Sit813 V H T i A L K)
    (hNV : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G))
    (hnat : IsNaturalSL2Module K (u1Grp V H T A K) (u1Grp V H T A K ⊓ centralizer (K : Set G)))
    (h4 : Nat.card (v1Grp V H T A K) = 4)
    (hKV : ∀ x ∈ V, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ u1Grp V H T A K) {c : G}
    (hc3 : IsPGroup 3 ↥(Subgroup.zpowers c)) (hcV : c ∈ normalizer (V : Set G))
    (hcK : c ∈ normalizer (K : Set G))
    (hc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K) :
    V ≤ centralizer ({c} : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := CFSG.Quasithin.A10.card_modEq_card_inf_centralizer (p := 3) (B := V) (g := c) hcV
    hc3
  rw [h.card_V_eq_eight] at hmod
  have hdvd : Nat.card ↥(V ⊓ centralizer ({c} : Set G)) ∣ 8 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ centralizer ({c} : Set G) ≤ V)
    rwa [h.card_V_eq_eight] at this
  have hmod' : Nat.card ↥(V ⊓ centralizer ({c} : Set G)) % 3 = 2 := by
    unfold Nat.ModEq at hmod
    omega
  have hne : ∃ v₀ ∈ V, v₀ ≠ 1 ∧ c * v₀ = v₀ * c := by
    by_contra hno
    push Not at hno
    have hbot : V ⊓ centralizer ({c} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact hno x hxV hx1 (Subgroup.mem_centralizer_iff.mp hxC c (Set.mem_singleton c))
    rw [hbot, Subgroup.card_bot] at hmod'
    omega
  obtain ⟨v₀, hv₀V, hv₀1, hv₀c⟩ := hne
  obtain ⟨k₀, hk₀K, hk₀⟩ := h.exists_comm_not_mem_u1Grp_inf_centralizer hv₀V hv₀1
  have hexe : ∃ e : G, e ∈ u1Grp V H T A K ∧
      e ∉ u1Grp V H T A K ⊓ centralizer (K : Set G) ∧ c * e * c⁻¹ = e := by
    refine ⟨k₀ * v₀ * k₀⁻¹ * v₀⁻¹, hKV v₀ hv₀V k₀ hk₀K, hk₀, ?_⟩
    have h1 := h.conj_mul_conj_of_comm_mem_oTwoMod hNV hcV hcK hc hk₀K (Sit813.V_le_uGrp hv₀V)
    have hv₀fix : c * v₀ * c⁻¹ = v₀ := by rw [hv₀c]; group
    rw [hv₀fix] at h1
    calc c * (k₀ * v₀ * k₀⁻¹ * v₀⁻¹) * c⁻¹
        = (c * (k₀ * v₀ * k₀⁻¹) * c⁻¹) * (c * v₀ * c⁻¹)⁻¹ := by group
      _ = k₀ * v₀ * k₀⁻¹ * v₀⁻¹ := by rw [h1, hv₀fix]
  obtain ⟨e, heU₁, heD, hcfix⟩ := hexe
  obtain ⟨F, hF, hFfin, hcard, φ, ψ, hφ, hψ, hker, heq⟩ := hnat
  have hcU : c ∈ normalizer (uGrp V K : Set G) :=
    mem_normalizer_conjClosure_of_mem_normalizers hcV hcK
  have hV₁ : ∀ v₁ ∈ v1Grp V H T A K, c * v₁ = v₁ * c := by
    intro v₁ hv₁
    by_cases hv₁1 : v₁ = 1
    · rw [hv₁1]; simp
    have hv₁U₁ : v₁ ∈ u1Grp V H T A K := Sit813.v1Grp_le_u1Grp hv₁
    have hv₁V : v₁ ∈ V := Sit813.v1Grp_le_V hv₁
    have hv₁D : v₁ ∉ u1Grp V H T A K ⊓ centralizer (K : Set G) := by
      intro hD
      exact hv₁1 (h.eq_one_of_centralizes_K hv₁V fun k hk =>
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hD).2 k hk)
    have ha : Multiplicative.toAdd (ψ ⟨v₁, hv₁U₁⟩) ≠ 0 := by
      intro h0
      apply hv₁D
      have : ψ ⟨v₁, hv₁U₁⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        simpa using h0
      exact (hker ⟨v₁, hv₁U₁⟩).mp this
    have hb : Multiplicative.toAdd (ψ ⟨e, heU₁⟩) ≠ 0 := by
      intro h0
      apply heD
      have : ψ ⟨e, heU₁⟩ = 1 := by
        apply Multiplicative.toAdd.injective
        simpa using h0
      exact (hker ⟨e, heU₁⟩).mp this
    obtain ⟨g, hg⟩ := sl2_exists_mulVec_eq hb ha
    obtain ⟨k, hk⟩ := hφ g
    have hkU₁ : (k : G) * e * (k : G)⁻¹ ∈ u1Grp V H T A K :=
      (Subgroup.mem_normalizer_iff.mp (Sit813.k_le_normalizer_u1Grp k.2) e).mp heU₁
    have hψ1 := heq k ⟨e, heU₁⟩ ⟨(k : G) * e * (k : G)⁻¹, hkU₁⟩ rfl
    rw [hk, hg] at hψ1
    have hψ2 : ψ ⟨(k : G) * e * (k : G)⁻¹, hkU₁⟩ = ψ ⟨v₁, hv₁U₁⟩ :=
      Multiplicative.toAdd.injective hψ1
    have hdD : ((k : G) * e * (k : G)⁻¹)⁻¹ * v₁ ∈
        u1Grp V H T A K ⊓ centralizer (K : Set G) := by
      have : ψ (⟨(k : G) * e * (k : G)⁻¹, hkU₁⟩⁻¹ * ⟨v₁, hv₁U₁⟩) = 1 := by
        rw [map_mul, map_inv, hψ2, inv_mul_cancel]
      exact (hker _).mp this
    obtain ⟨d, hdD', hv₁eq⟩ : ∃ d ∈ u1Grp V H T A K ⊓ centralizer (K : Set G),
        v₁ = ((k : G) * e * (k : G)⁻¹) * d := ⟨_, hdD, by group⟩
    have hcfix' : c * ((k : G) * e * (k : G)⁻¹) * c⁻¹ = (k : G) * e * (k : G)⁻¹ := by
      have h1 := h.conj_mul_conj_of_comm_mem_oTwoMod hNV hcV hcK hc k.2
        (Sit813.u1Grp_le_uGrp heU₁)
      rw [hcfix] at h1
      exact h1
    have he'U : (k : G) * e * (k : G)⁻¹ ∈ uGrp V K := Sit813.u1Grp_le_uGrp hkU₁
    have hdU : d ∈ uGrp V K := Sit813.u1Grp_le_uGrp (Subgroup.mem_inf.mp hdD').1
    have hdC : d ∈ centralizer (K : Set G) := (Subgroup.mem_inf.mp hdD').2
    have hcdU : c * d * c⁻¹ ∈ uGrp V K := (Subgroup.mem_normalizer_iff.mp hcU d).mp hdU
    have hcomm' : ((k : G) * e * (k : G)⁻¹) * ((c * d * c⁻¹) * d⁻¹) =
        ((c * d * c⁻¹) * d⁻¹) * ((k : G) * e * (k : G)⁻¹) :=
      h.isElemAbelian_uGrp.comm he'U ((uGrp V K).mul_mem hcdU ((uGrp V K).inv_mem hdU))
    have hw : c * v₁ * c⁻¹ * v₁⁻¹ = (c * d * c⁻¹) * d⁻¹ := by
      calc c * v₁ * c⁻¹ * v₁⁻¹
          = (c * ((k : G) * e * (k : G)⁻¹) * c⁻¹) * (c * d * c⁻¹) *
              (((k : G) * e * (k : G)⁻¹) * d)⁻¹ := by rw [hv₁eq]; group
        _ = ((k : G) * e * (k : G)⁻¹) * (c * d * c⁻¹) *
              (((k : G) * e * (k : G)⁻¹) * d)⁻¹ := by rw [hcfix']
        _ = (((k : G) * e * (k : G)⁻¹) * ((c * d * c⁻¹) * d⁻¹)) *
              ((k : G) * e * (k : G)⁻¹)⁻¹ := by group
        _ = (((c * d * c⁻¹) * d⁻¹) * ((k : G) * e * (k : G)⁻¹)) *
              ((k : G) * e * (k : G)⁻¹)⁻¹ := by rw [hcomm']
        _ = (c * d * c⁻¹) * d⁻¹ := by group
    have hwV : c * v₁ * c⁻¹ * v₁⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp hcV v₁).mp hv₁V) (V.inv_mem hv₁V)
    have hcdC : c * d * c⁻¹ ∈ centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      have hk'' : c⁻¹ * k' * c ∈ K := by
        have h1 := (Subgroup.mem_normalizer_iff.mp hcK (c⁻¹ * k' * c)).mpr
        have h2 : c * (c⁻¹ * k' * c) * c⁻¹ = k' := by group
        rw [h2] at h1
        exact h1 hk'
      have hc1 := Subgroup.mem_centralizer_iff.mp hdC _ hk''
      calc k' * (c * d * c⁻¹) = c * ((c⁻¹ * k' * c) * d) * c⁻¹ := by group
        _ = c * (d * (c⁻¹ * k' * c)) * c⁻¹ := by rw [hc1]
        _ = (c * d * c⁻¹) * k' := by group
    have hwC : c * v₁ * c⁻¹ * v₁⁻¹ ∈ centralizer (K : Set G) := by
      rw [hw]
      exact (centralizer (K : Set G)).mul_mem hcdC ((centralizer (K : Set G)).inv_mem hdC)
    have hw1 : c * v₁ * c⁻¹ * v₁⁻¹ = 1 :=
      h.eq_one_of_centralizes_K hwV fun k' hk' => Subgroup.mem_centralizer_iff.mp hwC k' hk'
    calc c * v₁ = (c * v₁ * c⁻¹ * v₁⁻¹) * (v₁ * c) := by group
      _ = v₁ * c := by rw [hw1, one_mul]
  have hle : v1Grp V H T A K ≤ V ⊓ centralizer ({c} : Set G) := fun v₁ hv₁ =>
    Subgroup.mem_inf.mpr ⟨Sit813.v1Grp_le_V hv₁, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hV₁ v₁ hv₁⟩
  have h4dvd : 4 ∣ Nat.card ↥(V ⊓ centralizer ({c} : Set G)) := by
    rw [← h4]
    exact Subgroup.card_dvd_of_le hle
  have hm8 : Nat.card ↥(V ⊓ centralizer ({c} : Set G)) = 8 := by
    have : Nat.card ↥(V ⊓ centralizer ({c} : Set G)) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have heq' : V ⊓ centralizer ({c} : Set G) = V :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm8, h.card_V_eq_eight])
  intro v hv
  have : v ∈ V ⊓ centralizer ({c} : Set G) := by rw [heq']; exact hv
  exact (Subgroup.mem_inf.mp this).2

theorem Sit813.mem_centralizer_uGrp_of_comm_mem_oTwoMod (h : Sit813 V H T i A L K)
    (hNV : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G))
    (hnat : IsNaturalSL2Module K (u1Grp V H T A K) (u1Grp V H T A K ⊓ centralizer (K : Set G)))
    (h4 : Nat.card (v1Grp V H T A K) = 4)
    (hKV : ∀ x ∈ V, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ u1Grp V H T A K) {c : G}
    (hc3 : IsPGroup 3 ↥(Subgroup.zpowers c)) (hcV : c ∈ normalizer (V : Set G))
    (hcK : c ∈ normalizer (K : Set G))
    (hc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ oTwoMod (cGrp H T) K) :
    c ∈ centralizer (uGrp V K : Set G) := by
  have hV := h.centralizes_V_of_comm_mem_oTwoMod hNV hnat h4 hKV hc3 hcV hcK hc
  have hle : uGrp V K ≤ centralizer ({c} : Set G) := by
    refine conjClosure_le fun k hk x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hcx : c * x = x * c := Subgroup.mem_centralizer_iff.mp (hV hx) c (Set.mem_singleton c)
    have hcx' : c * x * c⁻¹ = x := by rw [hcx]; group
    have h1 := h.conj_mul_conj_of_comm_mem_oTwoMod hNV hcV hcK hc hk (Sit813.V_le_uGrp hx)
    rw [hcx'] at h1
    calc c * (k * x * k⁻¹) = (c * (k * x * k⁻¹) * c⁻¹) * c := by group
      _ = (k * x * k⁻¹) * c := by rw [h1]
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (hle hu) c (Set.mem_singleton c)).symm

end Sit

end CFSG.LocalAnalysis.WeakClosure81

end
