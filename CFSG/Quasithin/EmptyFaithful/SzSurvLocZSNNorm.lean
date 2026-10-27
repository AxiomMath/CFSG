module

public import CFSG.Quasithin.Recognition.SzR1MNUNorm

public section

namespace CFSG.Quasithin.SzSurvLoc

open CFSG.Quasithin.SzR1.MNU

theorem mem_of_central_involution_of_commutator
    {G : Type} [Group G] [Finite G] {P S Q A K1 Zs : Subgroup G}
    (hSP : S ≤ P) (hS3 : S.relIndex P = 3) (hS2 : IsPGroup 2 S) (hQS : Q ≤ S)
    (hQ2 : Q.relIndex S = 2) (hQn : P ≤ Subgroup.normalizer (Q : Set G))
    (hAn : P ≤ Subgroup.normalizer (A : Set G)) (hAS : A ≤ S)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hAQ : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a)
    (hE1 : ∀ s ∈ S, ∀ x ∈ A, s * x * s⁻¹ * x⁻¹ ∈ Zs)
    (hKZ : ∀ n ∈ S, n * n = 1 → (∀ s ∈ S, n * s = s * n) → ∀ k ∈ K1, k * n = n * k)
    (hO2 : ∀ N : Subgroup G, IsPGroup 2 N → N ≤ S →
      K1 ⊔ P ≤ Subgroup.normalizer (N : Set G) → N = ⊥)
    {u : G} (huA : u ∈ A) (huc : ∀ s ∈ S, u * s = s * u) : u ∈ Zs := by
  have hApG : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hA2 g g.2)⟩
  have hyQc : ∀ q ∈ Q, u * q = q * u := hAQ u huA
  obtain ⟨a, haP, ha3, haS⟩ := Norm.exists_order_three hS3 hS2
  have haQ : a ∉ Q := fun h => haS (hQS h)
  have hPgen : S ⊔ Subgroup.zpowers a = P := Norm.sup_zpowers_eq hS3 hSP haP haS
  have hgen : ∀ H : Subgroup G, S ≤ H → a ∈ H → P ≤ H := fun H hSH haH =>
    hPgen.ge.trans (sup_le hSH (Subgroup.zpowers_le.mpr haH))
  have hconj : ∀ s ∈ S, s * a * s⁻¹ ∈ Q ⊔ Subgroup.zpowers a := fun s hs =>
    Norm.conj_mem_sup_zpowers hSP hQS hS3 hQ2 hS2 hQn haP ha3 hs
  have ha2 : a * a = a⁻¹ := eq_inv_of_mul_eq_one_left (Norm.cube_eq_one ha3)
  obtain ⟨v, hv⟩ : ∃ v : G, v = a * u * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : G, w = a⁻¹ * u * a := ⟨_, rfl⟩
  have hvA : v ∈ A := by
    rw [hv]
    exact (Subgroup.mem_normalizer_iff.mp (hAn haP) u).mp huA
  have hwA : w ∈ A := by
    rw [hw]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hAn (P.inv_mem haP)) u).mp huA
    simpa using h1
  have hv2 : v * v = 1 := hA2 v hvA
  have hw2 : w * w = 1 := hA2 w hwA
  have hu2 : u * u = 1 := hA2 u huA
  have hyv : u * v = v * u := hAab u huA v hvA
  have hyw : u * w = w * u := hAab u huA w hwA
  have hvw : v * w = w * v := hAab v hvA w hwA
  have hav : a * u * a⁻¹ = v := hv.symm
  have hawv : a * v * a⁻¹ = w := by
    rw [hv, hw]
    calc a * (a * u * a⁻¹) * a⁻¹ = (a * a) * u * (a * a)⁻¹ := by group
      _ = a⁻¹ * u * a := by rw [ha2, inv_inv]
  have haw : a * w * a⁻¹ = u := by
    rw [hw]
    group
  have hn_a : a * (u * v * w) * a⁻¹ = u * v * w :=
    Norm.conj_prod_cyc hyv hyw hav hawv haw
  have hsu : ∀ s ∈ S, s * u * s⁻¹ = u := fun s hs => by
    rw [← huc s hs, mul_inv_cancel_right]
  have hswap : ∀ s ∈ S, (s * v * s⁻¹ = v ∧ s * w * s⁻¹ = w) ∨
      (s * v * s⁻¹ = w ∧ s * w * s⁻¹ = v) := fun s hs =>
    Norm.swap_or_fix hSP hQn haP haQ ha3 hyQc hs (huc s hs) (hconj s hs) hv hw
  have hn_s : ∀ s ∈ S, s * (u * v * w) * s⁻¹ = u * v * w := fun s hs =>
    Norm.conj_prod_swap hvw (hsu s hs) (hswap s hs)
  have hnA : u * v * w ∈ A := A.mul_mem (A.mul_mem huA hvA) hwA
  have hnS : u * v * w ∈ S := hAS hnA
  have hnn : u * v * w * (u * v * w) = 1 := Norm.prod_mul_self hu2 hv2 hw2 hyv hyw hvw
  have hPn : P ≤ Subgroup.normalizer ((Subgroup.zpowers (u * v * w) : Subgroup G) : Set G) :=
    hgen _ (fun s hs => Norm.mem_normalizer_zpowers (Norm.comm_of_conj_eq (hn_s s hs)))
      (Norm.mem_normalizer_zpowers (Norm.comm_of_conj_eq hn_a))
  have hKn : ∀ k ∈ K1, k * (u * v * w) = (u * v * w) * k :=
    hKZ _ hnS hnn (fun s hs => Norm.comm_of_conj_eq (hn_s s hs))
  have hKPn : K1 ⊔ P ≤ Subgroup.normalizer ((Subgroup.zpowers (u * v * w) : Subgroup G) : Set G) :=
    sup_le (fun k hk => Norm.mem_normalizer_zpowers (hKn k hk).symm) hPn
  have hzle : Subgroup.zpowers (u * v * w) ≤ A := Subgroup.zpowers_le.mpr hnA
  have hn1 : u * v * w = 1 := by
    have hbot := hO2 _ (hApG.to_le hzle) (hzle.trans hAS) hKPn
    have hmem : u * v * w ∈ Subgroup.zpowers (u * v * w) := Subgroup.mem_zpowers _
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hwyv : w = u * v := by
    have h1 : w = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right hn1
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hu2]
    exact hyv.symm
  by_cases hfix : ∀ s ∈ S, s * v * s⁻¹ = v
  ·
    have huN : u ∈ Subgroup.closure ({u, v} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hvN : v ∈ Subgroup.closure ({u, v} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hwN : w ∈ Subgroup.closure ({u, v} : Set G) := by
      rw [hwyv]
      exact Subgroup.mul_mem _ huN hvN
    have hNA : Subgroup.closure ({u, v} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with h | h
      · rw [h]
        exact huA
      · rw [Set.mem_singleton_iff.mp h]
        exact hvA
    have hSN : S ≤ Subgroup.normalizer
        ((Subgroup.closure ({u, v} : Set G) : Subgroup G) : Set G) := by
      intro s hs
      refine Norm.mem_normalizer_closure_pair ?_ ?_
      · rw [hsu s hs]
        exact huN
      · rw [hfix s hs]
        exact hvN
    have haN : a ∈ Subgroup.normalizer
        ((Subgroup.closure ({u, v} : Set G) : Subgroup G) : Set G) := by
      refine Norm.mem_normalizer_closure_pair ?_ ?_
      · rw [hav]
        exact hvN
      · rw [hawv]
        exact hwN
    have hPN : P ≤ Subgroup.normalizer
        ((Subgroup.closure ({u, v} : Set G) : Subgroup G) : Set G) := hgen _ hSN haN
    have hvS : v ∈ S := hAS hvA
    have hKv : ∀ k ∈ K1, k * v = v * k :=
      hKZ v hvS hv2 (fun s hs => Norm.comm_of_conj_eq (hfix s hs))
    have hKuS : ∀ k ∈ K1, k * u * k⁻¹ = u := fun k hk => by
      rw [hKZ u (hAS huA) hu2 huc k hk, mul_inv_cancel_right]
    have hKvS : ∀ k ∈ K1, k * v * k⁻¹ = v := fun k hk => by
      rw [hKv k hk, mul_inv_cancel_right]
    have hKN : K1 ≤ Subgroup.normalizer
        ((Subgroup.closure ({u, v} : Set G) : Subgroup G) : Set G) := by
      intro k hk
      refine Norm.mem_normalizer_closure_pair ?_ ?_
      · rw [hKuS k hk]
        exact huN
      · rw [hKvS k hk]
        exact hvN
    have hbot := hO2 _ (hApG.to_le hNA) (hNA.trans hAS) (sup_le hKN hPN)
    have hmem := huN
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem]
    exact Zs.one_mem
  ·
    push Not at hfix
    obtain ⟨s, hs, hsv⟩ := hfix
    rcases hswap s hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hsv
    · have h2 := hE1 s hs v hvA
      rw [h1, hwyv] at h2
      have e : u * v * v⁻¹ = u := by group
      rwa [e] at h2

end CFSG.Quasithin.SzSurvLoc
