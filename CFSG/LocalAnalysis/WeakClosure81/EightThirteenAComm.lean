module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenANorm
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenCommutator
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFiveMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_inf_C {X Y : Subgroup G} {g : G}
    (hX : g ∈ normalizer (X : Set G)) (hY : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨hnX, hnY⟩ := Subgroup.mem_inf.mp hn
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hX n).1 hnX,
    (Subgroup.mem_normalizer_iff.mp hY n).1 hnY⟩

private theorem mem_normalizer_centralizer_C {N : Subgroup G} {g : G}
    (hg : g ∈ normalizer (N : Set G)) :
    g ∈ normalizer ((centralizer (N : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hg' : g⁻¹ ∈ normalizer (N : Set G) := (normalizer (N : Set G)).inv_mem hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro n hn
  have hn' : g⁻¹ * n * g ∈ N := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hg' n).1 hn
    simpa using h1
  have hcomm := Subgroup.mem_centralizer_iff.mp hz _ hn'
  calc n * (g * z * g⁻¹) = g * ((g⁻¹ * n * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * n * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * z * g⁻¹) * n := by group

private theorem inv_mul_mem_of_relIndex_two {C V : Subgroup G} (hidx : C.relIndex V = 2)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hvC : v ∉ C) (hwC : w ∉ C) : v⁻¹ * w ∈ C := by
  have h2 : (C.subgroupOf V).index = 2 := hidx
  have key : (⟨v⁻¹, V.inv_mem hv⟩ * ⟨w, hw⟩ : ↥V) ∈ C.subgroupOf V := by
    rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact iff_of_false (fun h => hvC (by simpa using h)) hwC
  exact Subgroup.mem_subgroupOf.mp key

theorem Sit813.relIndex_centralizer_oTwoMod_ne_two {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    (V ⊓ centralizer (oTwoMod (cGrp H T) K : Set G)).relIndex V ≠ 2 := by
  intro hidx
  set N : Subgroup G := oTwoMod (cGrp H T) K with hNdef
  set C : Subgroup G := V ⊓ centralizer (N : Set G) with hCdef
  set U : Subgroup G := uGrp V K with hUdef
  set Z : Subgroup G := U ⊓ centralizer (N : Set G) with hZdef
  have D := h.fiveData
  have hKN : K ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le_self).mp h.oTwoMod_normal
  have hAN : A ≤ normalizer (N : Set G) := h.a_le_normalizer_oTwoMod
  have hZK : K ≤ normalizer (Z : Set G) := fun k hk =>
    mem_normalizer_inf_C (D.u_normK hk) (mem_normalizer_centralizer_C (hKN hk))
  have hZA : A ≤ normalizer (Z : Set G) := fun a ha =>
    mem_normalizer_inf_C (D.u_normA ha) (mem_normalizer_centralizer_C (hAN ha))
  have hVU : V ≤ U := le_conjClosure V K
  have hCZ : C ≤ Z := inf_le_inf_right _ hVU
  have hVC : ¬ V ≤ C := fun hle => by
    have h1 : C.relIndex V = 1 := Subgroup.relIndex_eq_one.mpr hle
    omega
  obtain ⟨v, hvV, hvC⟩ := SetLike.not_le_iff_exists.mp hVC
  have step1 : ∀ x ∈ normalizer (V : Set G), x ∈ normalizer (N : Set G) →
      v⁻¹ * (x * v * x⁻¹) ∈ C := by
    intro x hxV hxN
    have hxC : x ∈ normalizer (C : Set G) :=
      mem_normalizer_inf_C hxV (mem_normalizer_centralizer_C hxN)
    have hw : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).1 hvV
    have hwC : x * v * x⁻¹ ∉ C := fun hwC => hvC ((Subgroup.mem_normalizer_iff.mp hxC v).2 hwC)
    exact inv_mul_mem_of_relIndex_two hidx hvV hw hvC hwC
  have hmod := Five.five_conjugates_mod D hZK hZA hvV
    (fun k hk => hCZ (step1 k (Subgroup.mem_inf.mp hk).2 (hKN (Subgroup.mem_inf.mp hk).1)))
    (fun a ha => hCZ (step1 a (h.a_le_normalizer_V ha) (hAN ha)))
  obtain ⟨k, hkK, hkM⟩ : ∃ k ∈ K, k ∉ normalizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    have h1 : K ⊓ normalizer (V : Set G) = K := inf_of_le_left (fun k hk => hcon k hk)
    have h5 := h.concl813.d_index
    rw [h1, Subgroup.relIndex_self] at h5
    omega
  have hZk := hmod k hkK
  have hmain : ∀ n ∈ N, n * v * n⁻¹ = v := by
    intro n hn
    have hnM : n ∈ normalizer (V : Set G) := h.oTwoMod_le_normalizer hn
    have hm : k⁻¹ * n * k ∈ N := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hkK)) n).1 hn
      simpa using h1
    have hmM : k⁻¹ * n * k ∈ normalizer (V : Set G) := h.oTwoMod_le_normalizer hm
    have hc : n * (v⁻¹ * (k * v * k⁻¹)) = (v⁻¹ * (k * v * k⁻¹)) * n :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hZk).2 n hn
    have hc' : (v⁻¹ * (k * v * k⁻¹)) * n * (v⁻¹ * (k * v * k⁻¹))⁻¹ = n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.symm
    have hwV : v * (k⁻¹ * n * k) * v⁻¹ * (k⁻¹ * n * k)⁻¹ ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hmM v⁻¹).1 (V.inv_mem hvV)
      have h2 := V.mul_mem hvV h1
      simpa [mul_assoc] using h2
    have hx₀V : v * (n * v * n⁻¹)⁻¹ ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hnM v).1 hvV
      exact V.mul_mem hvV (V.inv_mem h1)
    have heq : k * (v * (k⁻¹ * n * k) * v⁻¹ * (k⁻¹ * n * k)⁻¹) * k⁻¹ =
        v * (n * v * n⁻¹)⁻¹ := by
      have e1 : k * (v * (k⁻¹ * n * k) * v⁻¹ * (k⁻¹ * n * k)⁻¹) * k⁻¹ =
          (k * v * k⁻¹) * n * (k * v * k⁻¹)⁻¹ * n⁻¹ := by group
      have hu : k * v * k⁻¹ = v * (v⁻¹ * (k * v * k⁻¹)) := by group
      rw [e1]
      generalize v⁻¹ * (k * v * k⁻¹) = c at hu hc'
      rw [hu]
      calc v * c * n * (v * c)⁻¹ * n⁻¹ = v * (c * n * c⁻¹) * v⁻¹ * n⁻¹ := by group
        _ = v * n * v⁻¹ * n⁻¹ := by rw [hc']
        _ = v * (n * v * n⁻¹)⁻¹ := by group
    have hw1 : v * (k⁻¹ * n * k) * v⁻¹ * (k⁻¹ * n * k)⁻¹ = 1 :=
      h.isTI_form k hkM _ hwV (heq ▸ hx₀V)
    have h0 : v * (n * v * n⁻¹)⁻¹ = 1 := by rw [← heq, hw1]; group
    exact (mul_inv_eq_one.mp h0).symm
  exact hvC (Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun n hn =>
    mul_inv_eq_iff_eq_mul.mp (hmain n hn)⟩)

theorem Sit813.exists_fixed_of_noncomm_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hN : ∃ n ∈ oTwoMod (cGrp H T) K, ∃ w ∈ V, n * w ≠ w * n) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ k ∈ K ⊓ normalizer (V : Set G), k * v * k⁻¹ = v := by
  set N : Subgroup G := oTwoMod (cGrp H T) K with hNdef
  set C : Subgroup G := V ⊓ centralizer (N : Set G) with hCdef
  have hKN : K ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le_self).mp h.oTwoMod_normal
  have hCV : C ≤ V := inf_le_left
  have hinv : ∀ k ∈ K ⊓ normalizer (V : Set G), ∀ c ∈ C, k * c * k⁻¹ ∈ C := by
    intro k hk c hc
    have hkC : k ∈ normalizer (C : Set G) :=
      mem_normalizer_inf_C (Subgroup.mem_inf.mp hk).2
        (mem_normalizer_centralizer_C (hKN (Subgroup.mem_inf.mp hk).1))
    exact (Subgroup.mem_normalizer_iff.mp hkC c).1 hc
  have h8 : Nat.card V = 8 := h.card_V_eq_eight
  have hrel : C.relIndex V * Nat.card C = Nat.card V := by
    simpa [inf_of_le_left hCV] using Subgroup.relIndex_mul_card (H := C) (K := V)
  have hne2 : C.relIndex V ≠ 2 := h.relIndex_centralizer_oTwoMod_ne_two
  obtain ⟨n, hn, w, hw, hnw⟩ := hN
  have hne1 : C.relIndex V ≠ 1 := by
    intro h1
    have hle : V ≤ C := Subgroup.relIndex_eq_one.mp h1
    exact hnw (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hle hw)).2 n hn)
  obtain ⟨z, hzV, hz1, hzN⟩ := h.exists_ne_one_mem_centralizer_oTwoMod
  have hzC : z ∈ C := Subgroup.mem_inf.mpr ⟨hzV, Subgroup.mem_centralizer_iff.mpr hzN⟩
  have hc1 : Nat.card C ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    exact hz1 (Subgroup.mem_bot.mp (h1 ▸ hzC))
  have hcard : Nat.card C = 2 := by
    rw [h8] at hrel
    obtain ⟨r, hr⟩ : ∃ r, r = C.relIndex V := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = Nat.card C := ⟨_, rfl⟩
    rw [← hr, ← hc] at hrel
    rw [← hr] at hne1 hne2
    rw [← hc] at hc1 ⊢
    have hr8 : r ≤ 8 := Nat.le_of_dvd (by norm_num) ⟨c, hrel.symm⟩
    interval_cases r <;> omega
  obtain ⟨y, hy1, huniq⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hcard
  refine ⟨(y : G), hCV y.2, fun h' => hy1 (Subtype.ext h'), fun k hk => ?_⟩
  have hkC : k * (y : G) * k⁻¹ ∈ C := hinv k hk y y.2
  have hne : (⟨k * (y : G) * k⁻¹, hkC⟩ : C) ≠ 1 := by
    intro h1
    apply hy1
    have h2 : k * (y : G) * k⁻¹ = 1 := congrArg Subtype.val h1
    have h3 : (y : G) = 1 := by
      have := congrArg (fun x => k⁻¹ * x * k) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  exact congrArg Subtype.val (huniq _ hne)

end CFSG.LocalAnalysis.WeakClosure81

end
