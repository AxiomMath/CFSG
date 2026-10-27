module

public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Background.G64ProofGroup

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {a : MulAut V}

omit [Finite V] in
theorem false_of_case5 (h : Hyp61 G a) (hC : B56Case5 (conjClosure (Subgroup.zpowers a) G)) :
    False := by
  obtain ⟨-, -, -, -, -, -, -, -, hidx, -⟩ := hC
  rw [commV_classK h, top_sup_eq, Subgroup.index_top] at hidx
  omega

theorem false_of_case4 (h : Hyp61 G a) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2)
    (hC : B56Case4 (conjClosure (Subgroup.zpowers a) G)) : False := by
  set K := conjClosure (Subgroup.zpowers a) G with hKdef
  obtain ⟨G₁, G₂, t, hK, h12, hcomm12, -, -, hdir1, -, ⟨-, hV12⟩, -, -, htN1, htN2, hout1,
    hout2⟩ := hC
  set V₁ := commV G₁ with hV₁
  set V₂ := commV G₂ with hV₂
  set D := transSet G a with hD
  have hDK : Subgroup.closure D = K := closure_transSet G a
  have hG₁K : G₁ ≤ K := by rw [hK]; exact le_sup_left.trans le_sup_left
  have hG₂K : G₂ ≤ K := by rw [hK]; exact le_sup_right.trans le_sup_left
  have htK : t ∈ K := by rw [hK]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hKN1 : K ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
    rw [hK]
    refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
    · exact le_normalizer_of_commute fun x hx y hy => (hcomm12 y hy x hx).symm
    · rw [Subgroup.zpowers_le]; exact htN1
  have hKN2 : K ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
    rw [hK]
    refine sup_le (sup_le (le_normalizer_of_commute hcomm12) Subgroup.le_normalizer) ?_
    rw [Subgroup.zpowers_le]; exact htN2
  have hinv1 : ∀ k ∈ K, ∀ v ∈ V₁, k v ∈ V₁ := fun k hk v hv =>
    G6.apply_mem_commV (fun x hx => (Subgroup.mem_normalizer_iff.1 (hKN1 hk) x).1 hx) hv
  have hinv2 : ∀ k ∈ K, ∀ v ∈ V₂, k v ∈ V₂ := fun k hk v hv =>
    G6.apply_mem_commV (fun x hx => (Subgroup.mem_normalizer_iff.1 (hKN2 hk) x).1 hx) hv
  set Kα := K ⊓ fixPt V₂ with hKα
  set Kβ := K ⊓ fixPt V₁ with hKβ
  have hnα : K ≤ Subgroup.normalizer (Kα : Set (MulAut V)) := by
    intro k hk
    refine mem_normalizer_of_conj_mem fun x hx => ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk),
      fun w hw => ?_⟩
    show k (x (k⁻¹ w)) = w
    rw [hx.2 _ (hinv2 _ (K.inv_mem hk) w hw)]
    simp
  have hnβ : K ≤ Subgroup.normalizer (Kβ : Set (MulAut V)) := by
    intro k hk
    refine mem_normalizer_of_conj_mem fun x hx => ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk),
      fun w hw => ?_⟩
    show k (x (k⁻¹ w)) = w
    rw [hx.2 _ (hinv1 _ (K.inv_mem hk) w hw)]
    simp
  have hαβ : Kα ⊓ Kβ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨hxK, hx2⟩, ⟨-, hx1⟩⟩ := hx
    rw [Subgroup.mem_bot]
    ext v
    have hv : v ∈ fixV K ⊔ (V₁ ⊔ V₂) := by rw [hdir1]; trivial
    obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul, map_mul, (mem_fixV.1 hc) x hxK, hx1 w₁ hw₁, hx2 w₂ hw₂]
    rfl
  have hcommαβ : ∀ x ∈ Kα, ∀ y ∈ Kβ, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ Kα ⊓ Kβ := by
      constructor
      · have h2 : y * x⁻¹ * y⁻¹ ∈ Kα :=
          (Subgroup.mem_normalizer_iff.1 (hnα hy.1) _).1 (Kα.inv_mem hx)
        have := Kα.mul_mem hx h2
        simpa [mul_assoc] using this
      · have h2 : x * y * x⁻¹ ∈ Kβ := (Subgroup.mem_normalizer_iff.1 (hnβ hx.1) y).1 hy
        exact Kβ.mul_mem h2 (Kβ.inv_mem hy)
    rw [hαβ, Subgroup.mem_bot] at h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hDsplit : ∀ d ∈ D, d ∈ Kα ∨ d ∈ Kβ := by
    intro d hd
    have hdK : d ∈ K := transSet_subset G a hd
    have hcard := card_commV_conj htr hd
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    obtain ⟨w₂, hw₂, hd2⟩ : ∃ w ∈ V₂, d w ≠ w := by
      by_contra hc
      push Not at hc
      exact hn1 ⟨hdK, hc⟩
    obtain ⟨w₁, hw₁, hd1⟩ : ∃ w ∈ V₁, d w ≠ w := by
      by_contra hc
      push Not at hc
      exact hn2 ⟨hdK, hc⟩
    have hx₁V : d w₁ * w₁⁻¹ ∈ V₁ := V₁.mul_mem (hinv1 d hdK w₁ hw₁) (V₁.inv_mem hw₁)
    have hx₂V : d w₂ * w₂⁻¹ ∈ V₂ := V₂.mul_mem (hinv2 d hdK w₂ hw₂) (V₂.inv_mem hw₂)
    have hx₁1 : d w₁ * w₁⁻¹ ≠ 1 := fun e => hd1 (mul_inv_eq_one.1 e)
    have hx₂1 : d w₂ * w₂⁻¹ ≠ 1 := fun e => hd2 (mul_inv_eq_one.1 e)
    have hne : d w₁ * w₁⁻¹ ≠ d w₂ * w₂⁻¹ := by
      intro e
      have : d w₁ * w₁⁻¹ ∈ V₁ ⊓ V₂ := ⟨hx₁V, e ▸ hx₂V⟩
      rw [hV12, Subgroup.mem_bot] at this
      exact hx₁1 this
    exact G6.false_of_card_two hcard (G6.mem_commV_of_mem (Subgroup.mem_zpowers d) w₁)
      (G6.mem_commV_of_mem (Subgroup.mem_zpowers d) w₂) hx₁1 hx₂1 hne
  have hG₁α : G₁ ≤ Kα := fun g hg => ⟨hG₁K hg, fun w hw => by
    have h1 : g w * w⁻¹ ∈ V₁ := G6.mem_commV_of_mem hg w
    have h2 : g w * w⁻¹ ∈ V₂ := V₂.mul_mem (hinv2 g (hG₁K hg) w hw) (V₂.inv_mem hw)
    have : g w * w⁻¹ ∈ V₁ ⊓ V₂ := ⟨h1, h2⟩
    rw [hV12, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.1 this⟩
  have hG₂β : G₂ ≤ Kβ := fun g hg => ⟨hG₂K hg, fun w hw => by
    have h1 : g w * w⁻¹ ∈ V₂ := G6.mem_commV_of_mem hg w
    have h2 : g w * w⁻¹ ∈ V₁ := V₁.mul_mem (hinv1 g (hG₂K hg) w hw) (V₁.inv_mem hw)
    have : g w * w⁻¹ ∈ V₁ ⊓ V₂ := ⟨h2, h1⟩
    rw [hV12, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.1 this⟩
  have hKle : K ≤ Kα ⊔ Kβ := by
    rw [← hDK, Subgroup.closure_le]
    intro d hd
    rcases hDsplit d hd with h | h
    · exact Subgroup.mem_sup_left h
    · exact Subgroup.mem_sup_right h
  have hαnβ : Kα ≤ Subgroup.normalizer (Kβ : Set (MulAut V)) := fun x hx => hnβ hx.1
  obtain ⟨tα, htα, tβ, htβ, htt⟩ := mem_sup_of_normalizer hαnβ (hKle htK)
  have hcomt : tα * tβ = tβ * tα := hcommαβ tα htα tβ htβ
  have htα1 : tα ∉ G₁ := by
    intro hmem
    apply hout1
    refine ⟨tα, hmem, fun x hx => ?_⟩
    rw [htt]
    have hx' : tβ * x = x * tβ := (hcommαβ x (hG₁α hx) tβ htβ).symm
    calc tα * tβ * x * (tα * tβ)⁻¹ = tα * (tβ * x) * tβ⁻¹ * tα⁻¹ := by group
      _ = tα * (x * tβ) * tβ⁻¹ * tα⁻¹ := by rw [hx']
      _ = tα * x * tα⁻¹ := by group
  have htβ2 : tβ ∉ G₂ := by
    intro hmem
    apply hout2
    refine ⟨tβ, hmem, fun x hx => ?_⟩
    rw [htt]
    have hx' : tα * (tβ * x * tβ⁻¹) = (tβ * x * tβ⁻¹) * tα :=
      hcommαβ tα htα _ (Kβ.mul_mem (Kβ.mul_mem htβ (hG₂β hx)) (Kβ.inv_mem htβ))
    calc tα * tβ * x * (tα * tβ)⁻¹ = (tα * (tβ * x * tβ⁻¹)) * tα⁻¹ := by group
      _ = (tβ * x * tβ⁻¹ * tα) * tα⁻¹ := by rw [hx']
      _ = tβ * x * tβ⁻¹ := by group
  have hztN1 : Subgroup.zpowers t ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
    rw [Subgroup.zpowers_le]; exact htN1
  have hztN2 : Subgroup.zpowers t ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
    rw [Subgroup.zpowers_le]; exact htN2
  have hztN : Subgroup.zpowers t ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) :
      Set (MulAut V)) := fun y hy => mem_normalizer_sup (hztN1 hy) (hztN2 hy)
  have h12n : G₁ ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := le_normalizer_of_commute hcomm12
  have hform : ∀ x ∈ K, ∃ g₁ ∈ G₁, ∃ g₂ ∈ G₂, ∃ j : ℤ, x = g₁ * g₂ * t ^ j := by
    intro x hx
    rw [hK, sup_comm] at hx
    obtain ⟨y, hy, n, hn, rfl⟩ := mem_sup_of_normalizer hztN hx
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := mem_sup_of_normalizer h12n hn
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨t ^ j * g₁ * (t ^ j)⁻¹, ?_, t ^ j * g₂ * (t ^ j)⁻¹, ?_, j, by group⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hztN1 (Subgroup.zpow_mem_zpowers t j)) g₁).1 hg₁
    · exact (Subgroup.mem_normalizer_iff.1 (hztN2 (Subgroup.zpow_mem_zpowers t j)) g₂).1 hg₂
  have htj : ∀ j : ℤ, t ^ j = tα ^ j * tβ ^ j := fun j => by
    rw [htt]
    exact (Commute.mul_zpow hcomt j)
  have hformβ : ∀ x ∈ Kβ, ∃ g₂ ∈ G₂, ∃ j : ℤ, x = g₂ * tβ ^ j := by
    intro x hx
    obtain ⟨g₁, hg₁, g₂, hg₂, j, hxe⟩ := hform x hx.1
    have hc : g₂ * tα ^ j = tα ^ j * g₂ :=
      (hcommαβ (tα ^ j) (Kα.zpow_mem htα j) g₂ (hG₂β hg₂)).symm
    have h1 : x = (g₁ * tα ^ j) * (g₂ * tβ ^ j) := by
      rw [hxe, htj]
      calc g₁ * g₂ * (tα ^ j * tβ ^ j) = g₁ * (g₂ * tα ^ j) * tβ ^ j := by group
        _ = g₁ * (tα ^ j * g₂) * tβ ^ j := by rw [hc]
        _ = _ := by group
    have h3 : g₁ * tα ^ j ∈ Kβ := by
      have : g₁ * tα ^ j = x * (g₂ * tβ ^ j)⁻¹ := by rw [h1]; group
      rw [this]
      exact Kβ.mul_mem hx (Kβ.inv_mem (Kβ.mul_mem (hG₂β hg₂) (Kβ.zpow_mem htβ j)))
    have h4 : g₁ * tα ^ j = 1 := by
      have : g₁ * tα ^ j ∈ Kα ⊓ Kβ := ⟨Kα.mul_mem (hG₁α hg₁) (Kα.zpow_mem htα j), h3⟩
      rw [hαβ, Subgroup.mem_bot] at this
      exact this
    exact ⟨g₂, hg₂, j, by rw [h1, h4, one_mul]⟩
  have hformα : ∀ x ∈ Kα, ∃ g₁ ∈ G₁, ∃ j : ℤ, x = g₁ * tα ^ j := by
    intro x hx
    obtain ⟨g₁, hg₁, g₂, hg₂, j, hxe⟩ := hform x hx.1
    have hc : g₂ * tα ^ j = tα ^ j * g₂ :=
      (hcommαβ (tα ^ j) (Kα.zpow_mem htα j) g₂ (hG₂β hg₂)).symm
    have h1 : x = (g₁ * tα ^ j) * (g₂ * tβ ^ j) := by
      rw [hxe, htj]
      calc g₁ * g₂ * (tα ^ j * tβ ^ j) = g₁ * (g₂ * tα ^ j) * tβ ^ j := by group
        _ = g₁ * (tα ^ j * g₂) * tβ ^ j := by rw [hc]
        _ = _ := by group
    have h3 : g₂ * tβ ^ j ∈ Kα := by
      have : g₂ * tβ ^ j = (g₁ * tα ^ j)⁻¹ * x := by rw [h1]; group
      rw [this]
      exact Kα.mul_mem (Kα.inv_mem (Kα.mul_mem (hG₁α hg₁) (Kα.zpow_mem htα j))) hx
    have h4 : g₂ * tβ ^ j = 1 := by
      have : g₂ * tβ ^ j ∈ Kα ⊓ Kβ := ⟨h3, Kβ.mul_mem (hG₂β hg₂) (Kβ.zpow_mem htβ j)⟩
      rw [hαβ, Subgroup.mem_bot] at this
      exact this
    exact ⟨g₁, hg₁, j, by rw [h1, h4, mul_one]⟩
  have hclβ : Subgroup.closure {d | d ∈ D ∧ d ∈ Kβ} = Kβ := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun d hd => hd.2
    · intro x hx
      exact mem_closure_inter_of_mem (by rw [inf_comm]; exact hαβ)
        (fun x hx y hy => (hcommαβ y hy x hx).symm) (fun d hd => (hDsplit d hd).symm)
        (hDK ▸ hx.1) hx
  have hclα : Subgroup.closure {d | d ∈ D ∧ d ∈ Kα} = Kα := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact fun d hd => hd.2
    · intro x hx
      exact mem_closure_inter_of_mem hαβ hcommαβ hDsplit (hDK ▸ hx.1) hx
  have htβsq : tβ ^ 2 ∈ G₂ := sq_mem_of_cyclic_mod hclβ
    (fun d hd => sq_of_mem_transSet h hd.1) (fun x hx => hKN2 hx.1) htβ hformβ
  have htαsq : tα ^ 2 ∈ G₁ := sq_mem_of_cyclic_mod hclα
    (fun d hd => sq_of_mem_transSet h hd.1) (fun x hx => hKN1 hx.1) htα hformα
  have ht2 : t ^ 2 ∈ G₁ ⊔ G₂ := by
    rw [htt, Commute.mul_pow hcomt 2]
    exact Subgroup.mul_mem_sup htαsq htβsq
  obtain ⟨g₁, hg₁, g₂, hg₂, j, hj⟩ := hform tα htα.1
  have hreduce : ∃ n ∈ G₁ ⊔ G₂, tα = n ∨ tα = n * t := by
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · refine ⟨g₁ * g₂ * t ^ j, ?_, Or.inl hj⟩
      have : t ^ j = (t ^ 2) ^ (j / 2) := by
        rw [← zpow_natCast, ← zpow_mul]
        congr 1
        omega
      rw [this]
      exact (G₁ ⊔ G₂).mul_mem (Subgroup.mul_mem_sup hg₁ hg₂) ((G₁ ⊔ G₂).zpow_mem ht2 _)
    · refine ⟨g₁ * g₂ * (t ^ 2) ^ (j / 2), ?_, Or.inr ?_⟩
      · exact (G₁ ⊔ G₂).mul_mem (Subgroup.mul_mem_sup hg₁ hg₂) ((G₁ ⊔ G₂).zpow_mem ht2 _)
      · have hj2 : t ^ j = (t ^ 2) ^ (j / 2) * t := by
          rw [← zpow_natCast, ← zpow_mul, ← zpow_add_one]
          congr 1
          omega
        rw [hj, hj2]
        group
  obtain ⟨n, hn, hn'⟩ := hreduce
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_sup_of_normalizer h12n hn
  rcases hn' with he | he
  ·
    have hm : h₂ ∈ Kα ⊓ Kβ := by
      refine ⟨?_, hG₂β hh₂⟩
      have : h₂ = h₁⁻¹ * tα := by rw [he]; group
      rw [this]
      exact Kα.mul_mem (Kα.inv_mem (hG₁α hh₁)) htα
    rw [hαβ, Subgroup.mem_bot] at hm
    apply htα1
    rw [he, hm, mul_one]
    exact hh₁
  ·
    have hc : h₂ * tα = tα * h₂ := (hcommαβ tα htα h₂ (hG₂β hh₂)).symm
    have he' : tα⁻¹ * h₁⁻¹ * tα = h₂ * tβ := by
      have : tα = h₁ * tα * (h₂ * tβ) := by
        calc tα = h₁ * h₂ * (tα * tβ) := by rw [← htt]; exact he
          _ = h₁ * (h₂ * tα) * tβ := by group
          _ = h₁ * (tα * h₂) * tβ := by rw [hc]
          _ = h₁ * tα * (h₂ * tβ) := by group
      calc tα⁻¹ * h₁⁻¹ * tα = tα⁻¹ * h₁⁻¹ * (h₁ * tα * (h₂ * tβ)) := by rw [← this]
        _ = h₂ * tβ := by group
    have hm : h₂ * tβ ∈ Kα ⊓ Kβ := by
      refine ⟨?_, Kβ.mul_mem (hG₂β hh₂) htβ⟩
      rw [← he']
      exact Kα.mul_mem (Kα.mul_mem (Kα.inv_mem htα) (Kα.inv_mem (hG₁α hh₁))) htα
    rw [hαβ, Subgroup.mem_bot] at hm
    apply htβ2
    have : tβ = h₂⁻¹ := by
      calc tβ = h₂⁻¹ * (h₂ * tβ) := by group
        _ = h₂⁻¹ := by rw [hm, mul_one]
    rw [this]
    exact G₂.inv_mem hh₂

end CFSG.Quasithin.G64
