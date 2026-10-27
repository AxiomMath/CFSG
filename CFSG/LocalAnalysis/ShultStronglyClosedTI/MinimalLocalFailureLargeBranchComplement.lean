module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLargeBranchAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainBasic

public section

namespace CFSG.ShultStronglyClosedTI.FinalChain.LargeBranch

variable {G : Type} [Group G]

theorem conj_mem_of_normal {H A : Subgroup G} (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    {g : G} (hg : g ∈ H) {a : G} (ha : a ∈ A) : g * a * g⁻¹ ∈ A :=
  hAn.conj_mem ⟨a, hAH ha⟩ ha ⟨g, hg⟩

theorem exists_index_two_of_complement {H L B : Subgroup G} (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) (hBH : B ≤ H) (hHLB : H ≤ L ⊔ B) (hLB : L ⊓ B = ⊥)
    {B₀ : Subgroup B} (hB₀ : B₀.index = 2) : ∃ K : Subgroup H, K.index = 2 := by
  let N : Subgroup G := L ⊔ B₀.map B.subtype
  have hB₀H : B₀.map B.subtype ≤ H := (Subgroup.map_subtype_le _).trans hBH
  have hNB : ∀ b : B, (b : G) ∈ N → b ∈ B₀ := by
    intro b hbN
    obtain ⟨ℓ, hℓ, c, hc, hℓc⟩ := exists_mul_of_mem_sup hLH hLn hB₀H hbN
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    replace hℓc : ℓ * (c' : G) = b := hℓc
    have hℓB : ℓ ∈ B := by
      have heq : ℓ = (b : G) * (c' : G)⁻¹ := by
        rw [← hℓc]
        group
      rw [heq]
      exact B.mul_mem b.2 (B.inv_mem c'.2)
    have hℓ1 : ℓ = 1 := by
      have hmem : ℓ ∈ L ⊓ B := ⟨hℓ, hℓB⟩
      rwa [hLB, Subgroup.mem_bot] at hmem
    have hbc : b = c' := by
      apply Subtype.ext
      rw [← hℓc, hℓ1, one_mul]
    rw [hbc]
    exact hc'
  obtain ⟨a, ha, hab⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hB₀
  refine ⟨N.subgroupOf H, Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    ⟨⟨a, hBH a.2⟩, fun haN => ha (hNB a haN), fun g => ?_⟩⟩
  obtain ⟨ℓ, hℓ, b, hb, hℓb⟩ := exists_mul_of_mem_sup hLH hLn hBH (hHLB g.2)
  rcases hab ⟨b, hb⟩ with hba | hb0
  · left
    change (g : G) * a ∈ N
    rw [← hℓb, mul_assoc]
    exact N.mul_mem (Subgroup.mem_sup_left hℓ)
      (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨⟨b, hb⟩ * a, hba, rfl⟩))
  · right
    change (g : G) ∈ N
    rw [← hℓb]
    exact N.mul_mem (Subgroup.mem_sup_left hℓ)
      (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨⟨b, hb⟩, hb0, rfl⟩))

theorem sq_mem_of_conj_involution {H M A Q J : Subgroup G} {u : G} (hMH : M ≤ H)
    (hMn : (M.subgroupOf H).Normal) (hAM : A ≤ M) (hAn : (A.subgroupOf H).Normal) (hQA : Q ≤ A)
    (hJM : J ≤ M) (hJu : (J : Set G) = {1, u}) (hu2 : orderOf u = 2)
    (hinvA : ∀ a ∈ A, u * a * u⁻¹ = a⁻¹) (hRn : ((A ⊔ J).subgroupOf H).Normal)
    (hMsq : ∀ m ∈ M, m ^ 2 ∈ A ⊔ J)
    (hconj : ∀ v ∈ M, v ∉ Q → orderOf v = 2 → ∃ h ∈ H, h⁻¹ * v * h = u)
    (hCu : ∀ m ∈ M, m * u = u * m → m ∈ A ⊔ J) :
    ∀ m ∈ M, m ^ 2 ∈ A := by
  have hAH : A ≤ H := hAM.trans hMH
  have hJH : J ≤ H := hJM.trans hMH
  have huJ : u ∈ J := by
    rw [← SetLike.mem_coe, hJu]
    exact Or.inr rfl
  have hRform : ∀ r ∈ A ⊔ J, ∃ a ∈ A, r = a ∨ r = a * u := by
    intro r hr
    obtain ⟨a, ha, j, hj, rfl⟩ := exists_mul_of_mem_sup hAH hAn hJH hr
    have hj' : j ∈ (J : Set G) := hj
    rw [hJu] at hj'
    rcases hj' with rfl | rfl
    · exact ⟨a, ha, Or.inl (mul_one a)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  have huu : u * u = 1 := by
    rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hau : ∀ a ∈ A, (a * u) ^ 2 = 1 := by
    intro a ha
    calc (a * u) ^ 2 = a * (u * a * u⁻¹) * (u * u) := by rw [pow_two]; group
      _ = 1 := by rw [hinvA a ha, huu]; group
  have hcent : ∀ a ∈ A, a * u ∉ A → ∀ w ∈ M, w * (a * u) = a * u * w → w ∈ A ⊔ J := by
    intro a ha hvA w hw hwv
    have hvM : a * u ∈ M := M.mul_mem (hAM ha) (hJM huJ)
    have hv1 : a * u ≠ 1 := fun h1 => hvA (by rw [h1]; exact A.one_mem)
    obtain ⟨g, hg, hgv⟩ :=
      hconj _ hvM (fun hQ => hvA (hQA hQ)) (orderOf_eq_prime (hau a ha) hv1)
    have hw' : g⁻¹ * w * g ∈ M := by
      have hmem := conj_mem_of_normal hMH hMn (H.inv_mem hg) hw
      rwa [inv_inv] at hmem
    have hwu : g⁻¹ * w * g * u = u * (g⁻¹ * w * g) := by
      rw [← hgv]
      calc g⁻¹ * w * g * (g⁻¹ * (a * u) * g) = g⁻¹ * (w * (a * u)) * g := by group
        _ = g⁻¹ * (a * u * w) * g := by rw [hwv]
        _ = g⁻¹ * (a * u) * g * (g⁻¹ * w * g) := by group
    have hmem := conj_mem_of_normal (sup_le hAH hJH) hRn hg (hCu _ hw' hwu)
    rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at hmem
  intro m hm
  by_cases hmR : m ∈ A ⊔ J
  · obtain ⟨a, ha, rfl | rfl⟩ := hRform m hmR
    · exact A.pow_mem ha 2
    · rw [hau a ha]
      exact A.one_mem
  · by_contra hm2
    obtain ⟨a, ha, hma | hma⟩ := hRform _ (hMsq m hm)
    · exact hm2 (hma ▸ ha)
    · apply hmR
      apply hcent a ha (hma ▸ hm2) m hm
      rw [← hma, pow_two, mul_assoc]

theorem exists_index_two_of_large_branch {H M A B X J : Subgroup G} {u x₀ : G}
    (hMH : M ≤ H) (hMn : (M.subgroupOf H).Normal) (hAM : A ≤ M)
    (hAn : (A.subgroupOf H).Normal) (hsq : ∀ m ∈ M, m ^ 2 ∈ A)
    (hBH : B ≤ H) (hHMB : H ≤ M ⊔ B) (hJM : J ≤ M) (hJB : J ≤ B) (hMB : M ⊓ B ≤ J)
    (hJu : (J : Set G) = {1, u}) (huA : u ∉ A) (hMR : ¬ M ≤ A ⊔ J)
    (hXB : X ≤ B) (hx₀ : x₀ ∈ X) (hgen : ∀ y ∈ X, ∃ k : ℕ, y = x₀ ^ k) (hx₀1 : x₀ ≠ 1)
    {n : ℕ} (hn : Odd n) (hxn : x₀ ^ n = 1) (hxu : x₀ * u = u * x₀)
    (hXn : ∀ b ∈ B, b * x₀ * b⁻¹ ∈ X)
    (hreg : ∀ m ∈ M, m ∉ A ⊔ J → ∀ m' ∈ M, m' ∉ A ⊔ J →
      ∃! x : X, m'⁻¹ * ((x : G) * m * (x : G)⁻¹) ∈ A ⊔ J)
    {B₀ : Subgroup B} (hB₀ : B₀.index = 2) :
    ∃ K : Subgroup H, K.index = 2 := by
  have hAH : A ≤ H := hAM.trans hMH
  have hJH : J ≤ H := hJM.trans hMH
  have hx₀H : x₀ ∈ H := hBH (hXB hx₀)
  have huJ : u ∈ J := by
    rw [← SetLike.mem_coe, hJu]
    exact Or.inr rfl
  have huH : u ∈ H := hJH huJ
  have hcommA : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ A := by
    intro a ha b hb
    have heq : a * b * a⁻¹ * b⁻¹ = (a * b) ^ 2 * (b⁻¹ * (a ^ 2)⁻¹ * b⁻¹⁻¹) * (b ^ 2)⁻¹ := by
      simp only [pow_two]
      group
    rw [heq]
    exact A.mul_mem (A.mul_mem (hsq _ (M.mul_mem ha hb))
      (conj_mem_of_normal hAH hAn (H.inv_mem (hMH hb)) (A.inv_mem (hsq a ha))))
      (A.inv_mem (hsq b hb))
  let π : H →* H ⧸ A.subgroupOf H := QuotientGroup.mk' (A.subgroupOf H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπeq : ∀ g g' : H, π g = π g' ↔ (g : G)⁻¹ * g' ∈ A := fun g g' => by
    change (g : H ⧸ A.subgroupOf H) = g' ↔ _
    rw [QuotientGroup.eq]
    rfl
  have hπ1 : ∀ g : H, π g = 1 ↔ (g : G) ∈ A := fun g => by
    rw [← map_one π, hπeq]
    simp
  let V : Subgroup (H ⧸ A.subgroupOf H) := (M.subgroupOf H).map π
  have hVn : V.Normal := hMn.map π hπ
  have hV : ∀ v ∈ V, ∃ m : H, (m : G) ∈ M ∧ π m = v := fun v hv => by
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hv
    exact ⟨m, hm, rfl⟩
  have hcommV : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    obtain ⟨m, hm, rfl⟩ := hV v hv
    obtain ⟨m', hm', rfl⟩ := hV w hw
    rw [← map_mul, ← map_mul, hπeq]
    have hmem := hcommA _ (M.inv_mem hm') _ (M.inv_mem hm)
    convert hmem using 1
    push_cast
    group
  have hsqV : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := hV v hv
    rw [← map_pow, hπ1]
    exact hsq _ hm
  let xq : H ⧸ A.subgroupOf H := π ⟨x₀, hx₀H⟩
  have hxn' : xq ^ n = 1 := by
    rw [← map_pow, hπ1]
    change x₀ ^ n ∈ A
    rw [hxn]
    exact A.one_mem
  obtain ⟨Lq, hLqV, hDLq, hLqfix, hLqV', hLqpow⟩ :=
    exists_commutator_subgroup V hVn hcommV hsqV hn hxn'
  have hLqn : Lq.Normal := by
    constructor
    intro c hc γ
    obtain ⟨g, rfl⟩ := hπ γ
    obtain ⟨m, hm, b, hb, hmb⟩ := exists_mul_of_mem_sup hMH hMn hBH (hHMB g.2)
    have hg : g = ⟨m, hMH hm⟩ * ⟨b, hBH hb⟩ := Subtype.ext hmb.symm
    obtain ⟨k, hk⟩ := hgen _ (hXn b hb)
    have hbx : π ⟨b, hBH hb⟩ * xq * (π ⟨b, hBH hb⟩)⁻¹ = xq ^ k := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
      congr 1
      exact Subtype.ext (by push_cast; exact hk)
    have h1 := hLqpow _ k hbx c hc
    have h2 := hLqV' (π ⟨m, hMH hm⟩) (Subgroup.mem_map_of_mem π hm) _ h1
    rw [hg, map_mul]
    convert h2 using 1
    group
  let L : Subgroup G := (Lq.comap π).map H.subtype
  have hmemL : ∀ (g : G) (hg : g ∈ H), g ∈ L ↔ π ⟨g, hg⟩ ∈ Lq := by
    intro g hg
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hgL
      exact ⟨⟨g, hg⟩, hgL, rfl⟩
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hLn : (L.subgroupOf H).Normal := by
    have hsub : L.subgroupOf H = Lq.comap π :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [hsub]
    exact hLqn.comap π
  have hAL : A ≤ L := fun a ha => (hmemL a (hAH ha)).mpr (by
    rw [(hπ1 ⟨a, hAH ha⟩).mpr ha]
    exact Lq.one_mem)
  have hLM : L ≤ M := by
    intro g hgL
    have hgH := hLH hgL
    obtain ⟨m, hm, hmg⟩ := hV _ (hLqV ((hmemL g hgH).mp hgL))
    have hmA := (hπeq m ⟨g, hgH⟩).mp hmg
    have heq : g = m * ((m : G)⁻¹ * g) := by group
    rw [heq]
    exact M.mul_mem hm (hAM hmA)
  have huL : u ∉ L := by
    intro huL'
    have hcomm' : xq * π ⟨u, huH⟩ = π ⟨u, huH⟩ * xq := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxu
    exact huA ((hπ1 _).mp (hLqfix _ ((hmemL u huH).mp huL') hcomm'))
  have hLB : L ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgL, hgB⟩
    have hgJ : g ∈ (J : Set G) := hMB ⟨hLM hgL, hgB⟩
    rw [hJu] at hgJ
    rcases hgJ with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hgL huL
  have hRL : A ⊔ J ≤ L ⊔ J := sup_le_sup_right hAL J
  obtain ⟨m₁, hm₁M, hm₁R⟩ := Set.not_subset.mp hMR
  have hm₁H : m₁ ∈ H := hMH hm₁M
  have hℓ₀H : m₁⁻¹ * x₀ * m₁ * x₀⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hm₁H) hx₀H) hm₁H) (H.inv_mem hx₀H)
  have hℓ₀L : m₁⁻¹ * x₀ * m₁ * x₀⁻¹ ∈ L := by
    rw [hmemL _ hℓ₀H]
    have heq : (⟨m₁⁻¹ * x₀ * m₁ * x₀⁻¹, hℓ₀H⟩ : H) =
        (⟨m₁, hm₁H⟩ : H)⁻¹ * ⟨x₀, hx₀H⟩ * ⟨m₁, hm₁H⟩ * (⟨x₀, hx₀H⟩ : H)⁻¹ := rfl
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hDLq _ (Subgroup.mem_map_of_mem π hm₁M)
  have hℓ₀R : m₁⁻¹ * x₀ * m₁ * x₀⁻¹ ∉ A ⊔ J := by
    intro hℓ₀R
    obtain ⟨x, -, huniq⟩ := hreg m₁ hm₁M hm₁R m₁ hm₁M hm₁R
    have h1 : (1 : X) = x := huniq 1 (by simp)
    have h2 : (⟨x₀, hx₀⟩ : X) = x := huniq ⟨x₀, hx₀⟩ (by
      show m₁⁻¹ * (x₀ * m₁ * x₀⁻¹) ∈ A ⊔ J
      rw [show m₁⁻¹ * (x₀ * m₁ * x₀⁻¹) = m₁⁻¹ * x₀ * m₁ * x₀⁻¹ by group]
      exact hℓ₀R)
    exact hx₀1 (congrArg Subtype.val (h2.trans h1.symm))
  have hML : M ≤ L ⊔ J := by
    intro m hm
    by_cases hmR : m ∈ A ⊔ J
    · exact hRL hmR
    · obtain ⟨x, hx, -⟩ := hreg _ (hLM hℓ₀L) hℓ₀R m hm hmR
      have hxH : (x : G) ∈ H := hBH (hXB x.2)
      have hℓ₁ := conj_mem_of_normal hLH hLn hxH hℓ₀L
      have heq : m = (x : G) * (m₁⁻¹ * x₀ * m₁ * x₀⁻¹) * (x : G)⁻¹ *
          (m⁻¹ * ((x : G) * (m₁⁻¹ * x₀ * m₁ * x₀⁻¹) * (x : G)⁻¹))⁻¹ := by group
      rw [heq]
      exact (L ⊔ J).mul_mem (Subgroup.mem_sup_left hℓ₁) ((L ⊔ J).inv_mem (hRL hx))
  have hHLB : H ≤ L ⊔ B :=
    hHMB.trans (sup_le (hML.trans (sup_le le_sup_left (hJB.trans le_sup_right))) le_sup_right)
  exact exists_index_two_of_complement hLH hLn hBH hHLB hLB hB₀

end CFSG.ShultStronglyClosedTI.FinalChain.LargeBranch
