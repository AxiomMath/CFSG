module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem q8_comm_zpowers : ∀ a u : QuaternionGroup 2, u * u ≠ 1 → a * u = u * a →
    ∃ k : Fin 4, a = u ^ (k : ℕ) := by decide

theorem mem_zpowers_of_comm_B {P : Type*} [Group P] (d' : Q8SqData P) {u₀ : P}
    (hu₀A : u₀ ∈ d'.A) (hsq : u₀ * u₀ ≠ 1) {c : P} (hcu : c * u₀ = u₀ * c)
    (hcB : ∀ b ∈ d'.B, c * b = b * c) : c ∈ Subgroup.zpowers u₀ := by
  obtain ⟨a, ha, b₁, hb₁, rfl⟩ := d'.exists_mul c
  have hb₁c : ∀ b ∈ d'.B, b₁ * b = b * b₁ := by
    intro b hb
    have h2 := d'.mul_comm_of_mem ha hb
    have : a * (b₁ * b) = a * (b * b₁) := by
      calc a * (b₁ * b) = a * b₁ * b := by rw [mul_assoc]
        _ = b * (a * b₁) := hcB b hb
        _ = (b * a) * b₁ := by rw [mul_assoc]
        _ = (a * b) * b₁ := by rw [h2]
        _ = a * (b * b₁) := by rw [mul_assoc]
    exact mul_left_cancel this
  have hcA : a * b₁ ∈ d'.A := d'.A.mul_mem ha (d'.mem_A_of_central hb₁ hb₁c)
  have hyy : (d'.eA ⟨u₀, hu₀A⟩) * d'.eA ⟨u₀, hu₀A⟩ ≠ 1 := by
    intro h
    apply hsq
    have : (⟨u₀, hu₀A⟩ : ↥d'.A) * ⟨u₀, hu₀A⟩ = 1 := by
      apply d'.eA.injective; rw [map_mul, h, map_one]
    exact congrArg Subtype.val this
  have hxy : d'.eA ⟨a * b₁, hcA⟩ * d'.eA ⟨u₀, hu₀A⟩ = d'.eA ⟨u₀, hu₀A⟩ * d'.eA ⟨a * b₁, hcA⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg d'.eA (Subtype.ext hcu)
  obtain ⟨k, hk⟩ := q8_comm_zpowers _ _ hyy hxy
  have hk' : (⟨a * b₁, hcA⟩ : ↥d'.A) = ⟨u₀, hu₀A⟩ ^ (k : ℕ) := by
    apply d'.eA.injective; rw [map_pow]; exact hk
  have hk'' : a * b₁ = u₀ ^ (k : ℕ) := congrArg Subtype.val hk'
  rw [hk'']
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers u₀) _


section Bw

variable (h : Ctx T M g A t d x)

include h in
theorem exists_q8Data_u0 : ∃ d' : Q8SqData ↥(uOfL22 T M),
    (⟨u0Of d x, u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ⟩ : ↥(uOfL22 T M)) ∈ d'.A := by
  have hz1 := (dd_facts h.hd4).2
  have hu₀U := u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ
  have hu₀z := u0Of_sq h.c h.hD h.hd4 h.hx h.hx3
  obtain ⟨d₀⟩ := Q8SqData.nonempty_of_isQ8Sq h.c.c15.q8sq
  have hsqP : (⟨u0Of d x, hu₀U⟩ : ↥(uOfL22 T M)) * ⟨u0Of d x, hu₀U⟩ ≠ 1 := fun hh =>
    hz1 (hu₀z ▸ congrArg Subtype.val hh)
  rcases d₀.mem_A_or_mem_B hsqP with hA | hB
  · exact ⟨d₀, hA⟩
  · exact ⟨d₀.swap', hB⟩

include h in
theorem mem_K0_of_mem_U_comm {v : G} (hv : v ∈ uOfL22 T M)
    (hvu : v * u0Of d x = u0Of d x * v) : v ∈ K0 T d x := by
  have hvN := uOfL22_le_oTwoUpper h.c hv
  have hvd : v * d = d * v :=
    Subgroup.mem_centralizer_singleton_iff.mp (oTwoUpper_le_centralizer_d h.c h.hD h.hd4 hvN)
  refine ⟨hvN, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  rw [wOfX_eq_mul_u0Of]
  calc v * (d * u0Of d x) = (v * d) * u0Of d x := by rw [mul_assoc]
    _ = (d * v) * u0Of d x := by rw [hvd]
    _ = d * (v * u0Of d x) := by rw [mul_assoc]
    _ = d * (u0Of d x * v) := by rw [hvu]
    _ = (d * u0Of d x) * v := by rw [mul_assoc]

include h in
theorem mem_zpowers_u0_of_comm {d' : Q8SqData ↥(uOfL22 T M)}
    (hA : (⟨u0Of d x, u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ⟩ : ↥(uOfL22 T M)) ∈ d'.A)
    {c : G} (hc : c ∈ uOfL22 T M) (hcu : c * u0Of d x = u0Of d x * c)
    (hcB : ∀ b : ↥(uOfL22 T M), b ∈ d'.B → c * (b : G) = (b : G) * c) :
    c ∈ Subgroup.zpowers (u0Of d x) := by
  have hz1 := (dd_facts h.hd4).2
  have hu₀z := u0Of_sq h.c h.hD h.hd4 h.hx h.hx3
  have hsq : (⟨u0Of d x, u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ⟩ : ↥(uOfL22 T M)) *
      ⟨u0Of d x, u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ⟩ ≠ 1 := fun hh =>
    hz1 (hu₀z ▸ congrArg Subtype.val hh)
  have h1 := mem_zpowers_of_comm_B d' hA hsq (c := ⟨c, hc⟩) (Subtype.ext hcu)
    (fun b hb => Subtype.ext (hcB b hb))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

end Bw

end InspW2

end S143

end CFSG.Quasithin
