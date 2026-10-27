module

public import CFSG.Quasithin.Background.RonanE111HalfStep
public import CFSG.Quasithin.Background.RonanE111Syl
public import CFSG.Quasithin.Background.RonanE111MemE2

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R

variable {G : Type} [Group G] [Finite G]

theorem half_two {X T J : Subgroup G} (hR : E111Reduced G X T) (hJ : IsComp X J) {n : ℕ}
    (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁)
    (hsol : ∀ H : Subgroup G, T ≤ H → Group.IsSolvable ↥H → H ≤ G₁) {A₀ : Subgroup G}
    (hA₀T : A₀ ≤ T) (hA₀ab : IsElemAbelian 2 A₀)
    (hA₀S : ¬ A₀ ≤ T ⊓ Subgroup.normalizer (J : Set G))
    (hmem : ∀ K : Subgroup G, E1.IsE n ⊤ T A₀ K → K ≤ G₁) {W₀ : Subgroup G}
    (hW₀S : W₀ ≤ T ⊓ Subgroup.normalizer (J : Set G))
    (hSW₀ : T ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (W₀ : Set G))
    (hV₀ : A₀ ⊓ Subgroup.normalizer (J : Set G) ≤ W₀) :
    (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) ⊓ Subgroup.normalizer (W₀ : Set G) ≤ Cov G₁ J := by
  classical
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hSdef
  set M₀ : Subgroup G := (J ⊔ S) ⊓ Subgroup.normalizer (W₀ : Set G) with hM₀def
  by_contra hcon
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hSM₀ : S ≤ M₀ := le_inf le_sup_right hSW₀
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hS2 : IsPGroup 2 ↥S := hT.2.1.to_le hST
  have hSCov : S ≤ Cov G₁ J := fun s hs => mem_Cov_of_mem (hTG hs.1) hs.2
  obtain ⟨U, hU, hUmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun U : Subgroup G => S ≤ U ∧ U ≤ M₀ ∧ ¬ U ≤ Cov G₁ J)
    (fun U : Subgroup G => Nat.card U)
    ⟨M₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSM₀, le_rfl, hcon⟩⟩
  obtain ⟨hSU, hUM₀, hUCov⟩ := (Finset.mem_filter.mp hU).2
  have hUJS : U ≤ J ⊔ S := hUM₀.trans inf_le_left
  have hUW₀ : ∀ u ∈ U, ∀ w ∈ W₀, u * w * u⁻¹ ∈ W₀ := fun u hu w hw =>
    (Subgroup.mem_normalizer_iff.mp (hUM₀ hu).2 w).mp hw
  have hJS : J ⊔ S ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSN
  have hUJ : ∀ u ∈ U, u ∈ Subgroup.normalizer (J : Set G) := fun u hu => hJS (hUJS hu)
  have hSylU : IsSylowIn 2 S U := by
    have h1 := isSylowIn_compSup hR hJ
    refine ⟨hSU, hS2, fun h2 => h1.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex S U (J ⊔ S) hSU hUJS
    rw [← this]
    exact Dvd.dvd.mul_right h2 _
  obtain ⟨Y, hY, hYmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun Y : Subgroup G => Y ≤ U ∧ (∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) ∧
      Y ≤ Cov G₁ J)
    (fun Y : Subgroup G => Nat.card Y)
    ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bot_le, fun u _ y hy => by
      rw [Subgroup.mem_bot] at hy ⊢
      simp [hy], bot_le⟩⟩
  obtain ⟨hYU, hYn, hYCov⟩ := (Finset.mem_filter.mp hY).2
  have hYltU : Y < U := lt_of_le_of_ne hYU fun h => hUCov (h ▸ hYCov)
  obtain ⟨N, hN, hNmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun N : Subgroup G => N ≤ U ∧ (∀ u ∈ U, ∀ x ∈ N, u * x * u⁻¹ ∈ N) ∧ Y < N)
    (fun N : Subgroup G => Nat.card N)
    ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, fun u hu x hx =>
      U.mul_mem (U.mul_mem hu hx) (U.inv_mem hu), hYltU⟩⟩
  obtain ⟨hNU, hNn, hYN'⟩ := (Finset.mem_filter.mp hN).2
  have hYN : Y ≤ N := hYN'.le
  have hNCov : ¬ N ≤ Cov G₁ J := by
    intro hle
    have hmem : N ∈ Finset.univ.filter fun Y : Subgroup G => Y ≤ U ∧
        (∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) ∧ Y ≤ Cov G₁ J :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNU, hNn, hle⟩
    have h1 := hYmax N hmem
    exact hYN'.ne (Subgroup.eq_of_le_of_card_ge hYN h1)
  have hNchief : ∀ N' : Subgroup G, N' ≤ N → Y ≤ N' → (∀ u ∈ U, ∀ x ∈ N', u * x * u⁻¹ ∈ N') →
      N' = Y ∨ N' = N := by
    intro N' hN'N hYN' hN'n
    by_cases hN'Y : N' = Y
    · exact Or.inl hN'Y
    · right
      have hlt : Y < N' := lt_of_le_of_ne hYN' (Ne.symm hN'Y)
      have hmem : N' ∈ Finset.univ.filter fun N : Subgroup G => N ≤ U ∧
          (∀ u ∈ U, ∀ x ∈ N, u * x * u⁻¹ ∈ N) ∧ Y < N :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN'N.trans hNU, hN'n, hlt⟩
      exact Subgroup.eq_of_le_of_card_ge hN'N (hNmin N' hmem)
  have hKN : ∀ K : Subgroup G, S ≤ K → K ≤ U → N ≤ K ⊔ Y → K = U := by
    intro K hSK hKU hNK
    by_contra hKU'
    have hlt : Nat.card K < Nat.card U := by
      by_contra hge
      push Not at hge
      exact hKU' (Subgroup.eq_of_le_of_card_ge hKU hge)
    by_cases hKCov : K ≤ Cov G₁ J
    · exact hNCov (hNK.trans (sup_le hKCov hYCov))
    · have hmem : K ∈ Finset.univ.filter fun U : Subgroup G =>
          S ≤ U ∧ U ≤ M₀ ∧ ¬ U ≤ Cov G₁ J :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSK, hKU.trans hUM₀, hKCov⟩
      have := hUmin K hmem
      omega
  by_cases hD : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ Y
  ·
    have hle := le_sup_of_isTwoQuotient hSylU hNU hYN hNn hYn hD
    exact hNCov (hle.trans (sup_le hSCov hYCov))
  ·
    have hNJY : N ≤ J ⊔ Y := by
      have hnorm : ∀ u ∈ U, ∀ z ∈ N ⊓ (J ⊔ Y), u * z * u⁻¹ ∈ N ⊓ (J ⊔ Y) := by
        intro u hu z hz
        refine ⟨hNn u hu z hz.1, ?_⟩
        refine conj_mem_sup_of (x := u) (fun c hc => ?_) (fun c hc => ?_) hz.2
        · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hUJ u hu) c).mp hc)
        · exact Subgroup.mem_sup_right (hYn u hu c hc)
      rcases hNchief (N ⊓ (J ⊔ Y)) inf_le_left (le_inf hYN le_sup_right) hnorm with h | h
      · exfalso
        apply hD
        intro x hx
        obtain ⟨k, hk⟩ := pow_mem_of_mem_sup_two hSN hS2 (hUJS (hNU hx))
        refine ⟨k, ?_⟩
        have : x ^ 2 ^ k ∈ N ⊓ (J ⊔ Y) := ⟨N.pow_mem hx _, Subgroup.mem_sup_left hk⟩
        rwa [h] at this
      · exact fun x hx => (show x ∈ N ⊓ (J ⊔ Y) by rw [h]; exact hx).2
    set X : Subgroup G := N ⊓ J with hXdef
    set Y₀ : Subgroup G := J ⊓ Y with hY₀def
    have hXU : X ≤ U := inf_le_left.trans hNU
    have hXJ : X ≤ J := inf_le_right
    have hXN : X ≤ N := inf_le_left
    have hY₀X : Y₀ ≤ X := le_inf (inf_le_right.trans hYN) inf_le_left
    have hXn : ∀ u ∈ U, ∀ x ∈ X, u * x * u⁻¹ ∈ X := fun u hu x hx =>
      ⟨hNn u hu x hx.1, (Subgroup.mem_normalizer_iff.mp (hUJ u hu) x).mp hx.2⟩
    have hY₀n : ∀ u ∈ U, ∀ y ∈ Y₀, u * y * u⁻¹ ∈ Y₀ := fun u hu y hy =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hUJ u hu) y).mp hy.1, hYn u hu y hy.2⟩
    have hNXY : N ≤ X ⊔ Y := by
      intro x hx
      have hxJY : x ∈ Y ⊔ J := by rw [sup_comm]; exact hNJY hx
      obtain ⟨y, hy, j, hj, rfl⟩ := wr_mem_sup (H := Y) (K := J)
        (fun y hy j hj => (Subgroup.mem_normalizer_iff.mp (hUJ y (hYU hy)) j).mp hj) hxJY
      have hjN : j ∈ N := by
        have : j = y⁻¹ * (y * j) := by group
        rw [this]
        exact N.mul_mem (N.inv_mem (hYN hy)) hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy)
        (Subgroup.mem_sup_left (⟨hjN, hj⟩ : j ∈ N ⊓ J))
    have hne : Y₀ ≠ X := by
      intro h
      have hXY : X ≤ Y := by rw [← h]; exact inf_le_right
      exact not_le_of_gt hYN' (hNXY.trans (sup_le hXY le_rfl))
    have hUXS : U = X ⊔ S :=
      (hKN (X ⊔ S) le_sup_right (sup_le hXU hSU)
        (hNXY.trans (sup_le_sup_right le_sup_left _))).symm
    have hmin' : ∀ N' : Subgroup G, N' ≤ X → Y₀ ≤ N' →
        (∀ u ∈ U, ∀ x ∈ N', u * x * u⁻¹ ∈ N') → N' = Y₀ ∨ N' = X := by
      intro N' hN'X hY₀N' hN'n
      have hN'U : N' ≤ U := hN'X.trans hXU
      have hN'N : N' ⊔ Y ≤ N := sup_le (hN'X.trans hXN) hYN
      have hnorm : ∀ u ∈ U, ∀ z ∈ N' ⊔ Y, u * z * u⁻¹ ∈ N' ⊔ Y := fun u hu z hz =>
        conj_mem_sup_of (x := u) (fun c hc => Subgroup.mem_sup_left (hN'n u hu c hc))
          (fun c hc => Subgroup.mem_sup_right (hYn u hu c hc)) hz
      rcases hNchief (N' ⊔ Y) hN'N le_sup_right hnorm with h | h
      · left
        have : N' ≤ Y₀ := fun x hx =>
          ⟨hXJ (hN'X hx), (show x ∈ Y by rw [← h]; exact Subgroup.mem_sup_left hx)⟩
        exact le_antisymm this hY₀N'
      · right
        refine le_antisymm hN'X (fun x hx => ?_)
        have hxN'Y : x ∈ N' ⊔ Y := by rw [h]; exact hXN hx
        obtain ⟨n', hn', y, hy, rfl⟩ := wr_mem_sup (H := N') (K := Y)
          (fun a ha b hb => hYn a (hN'U ha) b hb) hxN'Y
        have hyX : y ∈ X := by
          have : y = n'⁻¹ * (n' * y) := by group
          rw [this]
          exact X.mul_mem (X.inv_mem (hN'X hn')) hx
        have hyY₀ : y ∈ Y₀ := ⟨hXJ hyX, hy⟩
        exact N'.mul_mem hn' (hY₀N' hyY₀)
    have hK' : ∀ K : Subgroup G, S ≤ K → K ≤ U → K ⊔ Y₀ = U → K = U := by
      intro K hSK hKU hK
      refine hKN K hSK hKU ?_
      calc N ≤ U := hNU
        _ = K ⊔ Y₀ := hK.symm
        _ ≤ K ⊔ Y := sup_le_sup_left inf_le_right _
    have hXCov := half_two_step hR hJ hn hTG hsol hA₀T hA₀ab hA₀S hmem hW₀S hV₀ hSU hUJS hUW₀
      hXU hXJ hY₀X hne hXn hY₀n hUXS hmin' hK' (inf_le_right.trans hYCov)
    exact hNCov (hNXY.trans (sup_le hXCov hYCov))

end CFSG.Quasithin.RonanE111
