module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalCount
public import CFSG.Timmesfeld.Bridge.RootStructWTIModule
public import CFSG.Timmesfeld.Bridge.RootStructR2Assembly

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

theorem two_mul_add_two_lt_two_pow {m : ℕ} (hm : 4 ≤ m) : 2 * m + 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

namespace TwoLocalSetting

variable {G : Type*} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem card_le_two_mul_card_inf_centralizer [Finite G] {a x y : G} (ha : a ∈ D)
    {A : Subgroup G} (hAM : A ≤ nCore D a) (hx : x ∈ A) (hy : y ∈ nCore D a)
    (hyx : ¬ Commute y x) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer {y}) := by
  set A₀ := A ⊓ Subgroup.centralizer {y}
  have hsub : (A : Set G) ⊆ (A₀ : Set G) ∪ (fun z => x * z) '' (A₀ : Set G) := by
    intro z hz
    by_cases hyz : Commute y z
    · exact Or.inl ⟨hz, Subgroup.mem_centralizer_singleton_iff.2 hyz.eq.symm⟩
    · right
      refine ⟨x⁻¹ * z, ⟨A.mul_mem (A.inv_mem hx) hz, ?_⟩, by group⟩
      have h := (S.commute_mul_right_iff ha hy (hAM (A.inv_mem hx)) (hAM hz)).2
        (iff_of_false (fun h => hyx (Commute.inv_right_iff.1 h)) hyz)
      exact Subgroup.mem_centralizer_singleton_iff.2 h.eq.symm
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (A₀ : Set G) ((fun z => x * z) '' (A₀ : Set G))
  have h3 := Set.ncard_image_le (f := fun z => x * z) (s := (A₀ : Set G)) (Set.toFinite _)
  have e1 : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
  have e2 : Nat.card A₀ = (A₀ : Set G).ncard := Nat.card_coe_set_eq (A₀ : Set G)
  omega

theorem card_mul_card_centralizer_le {a : G} (ha : a ∈ D) (A : Subgroup G)
    (hAM : A ≤ nCore D a) :
    Nat.card A * Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card (nCore D a) * Nat.card ↥(A ⊓ Subgroup.centralizer (nCore D a : Set G)) := by
  have := S.hyp.finite
  set M := nCore D a
  induction h : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  subst h
  by_cases hZ : A ≤ Subgroup.centralizer (M : Set G)
  · rw [inf_eq_left.2 hZ, mul_comm]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le inf_le_left)
  obtain ⟨x, hxA, hxZ⟩ := Set.not_subset.1 hZ
  obtain ⟨y, hyM, hyx⟩ : ∃ y ∈ M, ¬ Commute y x := by
    by_contra hno
    push Not at hno
    exact hxZ (Subgroup.mem_centralizer_iff.2 fun y hy => (hno y hy).eq)
  set A₀ := A ⊓ Subgroup.centralizer {y}
  have hA₀A : A₀ ≤ A := inf_le_left
  have hxA₀ : x ∉ A₀ := fun h =>
    hyx (Subgroup.mem_centralizer_singleton_iff.1 h.2).symm
  have hlt : Nat.card A₀ < Nat.card A :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hA₀A fun h => hxA₀ (h ▸ hxA))
  have IH := ih _ hlt A₀ (hA₀A.trans hAM) rfl
  have h1 : Nat.card A ≤ 2 * Nat.card A₀ :=
    S.card_le_two_mul_card_inf_centralizer ha hAM hxA hyM hyx
  have hle : M ⊓ Subgroup.centralizer (A : Set G) ≤ M ⊓ Subgroup.centralizer (A₀ : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hA₀A)
  have hyC : y ∈ M ⊓ Subgroup.centralizer (A₀ : Set G) :=
    ⟨hyM, Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_singleton_iff.1 hz.2)⟩
  have hyC' : y ∉ M ⊓ Subgroup.centralizer (A : Set G) := fun h =>
    hyx (Subgroup.mem_centralizer_iff.1 h.2 x hxA).symm
  have h2 : 2 * Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card ↥(M ⊓ Subgroup.centralizer (A₀ : Set G)) :=
    two_mul_card_le_of_lt hle fun h => hyC' (h ▸ hyC)
  have h3 : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (M : Set G)) ≤
      Nat.card ↥(A ⊓ Subgroup.centralizer (M : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hA₀A)
  calc Nat.card A * Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G))
      ≤ 2 * Nat.card A₀ * Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G)) :=
        Nat.mul_le_mul_right _ h1
    _ = Nat.card A₀ * (2 * Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G))) := by ring
    _ ≤ Nat.card A₀ * Nat.card ↥(M ⊓ Subgroup.centralizer (A₀ : Set G)) :=
        Nat.mul_le_mul_left _ h2
    _ ≤ Nat.card M * Nat.card ↥(A₀ ⊓ Subgroup.centralizer (M : Set G)) := IH
    _ ≤ Nat.card M * Nat.card ↥(A ⊓ Subgroup.centralizer (M : Set G)) :=
        Nat.mul_le_mul_left _ h3

theorem card_mul_card_le {a : G} (ha : a ∈ D) (A : Subgroup G) (hAM : A ≤ nCore D a)
    (hA : ∀ x ∈ A, ∀ y ∈ A, Commute x y) :
    Nat.card A * Nat.card A ≤
      Nat.card (nCore D a) * Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)) := by
  have := S.hyp.finite
  have h := S.card_mul_card_centralizer_le ha A hAM
  have h1 : Nat.card A ≤ Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.card_le_of_le fun x hx =>
      ⟨hAM hx, Subgroup.mem_centralizer_iff.2 fun y hy => (hA y hy x hx).eq⟩
  have h2 : Nat.card ↥(A ⊓ Subgroup.centralizer (nCore D a : Set G)) ≤
      Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hAM)
  calc Nat.card A * Nat.card A
      ≤ Nat.card A * Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (A : Set G)) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ _ := h
    _ ≤ _ := Nat.mul_le_mul_left _ h2

theorem exists_not_commute {a e : G} (ha : a ∈ D) (he : e ∈ D) (hae : Commute a e) (hea : e ≠ a)
    (h2 : 2 ≤ (rootLines D a).ncard) : ∃ x ∈ D, Commute a x ∧ x ≠ a ∧ ¬ Commute x e := by
  classical
  obtain ⟨P, hPk, hP, hnc, -⟩ := S.exists_transversal ha
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < P.card)
  by_cases hxe : Commute x e
  · refine ⟨y, (hP y hy).1, (hP y hy).2.1, (hP y hy).2.2, fun hye => ?_⟩
    obtain ⟨hxD, hax, hxa⟩ := hP x hx
    obtain ⟨hyD, hay, hya⟩ := hP y hy
    rcases (S.commute_iff_eq_or_eq_mul ha hxD he hax hae hxa hea).1 hxe with h | h <;>
      rcases (S.commute_iff_eq_or_eq_mul ha hyD he hay hae hya hea).1 hye with h' | h'
    · exact hxy (h.symm.trans h')
    · refine hnc x hx y hy hxy ?_
      rw [← h, h']
      exact hay.mul_left (Commute.refl y)
    · refine hnc x hx y hy hxy ?_
      rw [← h', h]
      exact hax.symm.mul_right (Commute.refl x)
    · exact hxy (mul_left_cancel (h.symm.trans h'))
  · exact ⟨x, (hP x hx).1, (hP x hx).2.1, (hP x hx).2.2, hxe⟩

theorem commute_of_mem_lineN₀ {a d x y : G} (ha : a ∈ D) (hd : d ∈ D) (hda : d ≠ a)
    (hx : x ∈ lineN₀ D a d) (hy : y ∈ lineN₀ D a d) : Commute x y := by
  rw [commutatorElement_eq_one_iff_commute.symm]
  change x * y * x⁻¹ * y⁻¹ = 1
  rcases S.commutator_eq ha hx.1 hy.1 with h | h
  · exact h
  rcases S.commutator_eq hd hx.2 hy.2 with h' | h'
  · exact h'
  · exact absurd (h'.symm.trans h) hda

end TwoLocalSetting

theorem TwoLocalSetting.exists_ncard_rootLines {G : Type} [Group G] {D : Set G}
    (S : TwoLocalSetting G D) {a : G} (ha : a ∈ D) :
    ∃ n ≤ 3, (rootLines D a).ncard = 2 ^ n + 1 := by
  have := S.hyp.finite
  have hL := S.lineSetting
  have hD := S.root
  obtain ⟨n, hn⟩ := hL.exists_ncard_rootLines ha
  refine ⟨n, ?_, hn⟩
  by_contra hn3
  push Not at hn3
  set k := (rootLines D a).ncard
  have hk2 : 2 ≤ k := by rw [hn]; have := Nat.one_le_two_pow (n := n); omega
  obtain ⟨T, hT⟩ := hL.exists_mem_rootLines ha
  obtain ⟨d, hdD, had, hda, -⟩ := (S.mem_rootLines_iff ha).1 hT
  have hadD : a * d ∈ D := S.mul_mem_of_commute ha hdD had (Ne.symm hda)
  have hkd : (rootLines D d).ncard = k := ncard_rootLines_eq S.hyp.isClass ha hdD
  obtain ⟨x, hxD, hdx, hxd, hxa⟩ := S.exists_not_commute hdD ha had.symm (Ne.symm hda)
    (by rw [hkd]; exact hk2)
  have hxT : x ∉ rootGroup D d ⊔ rootGroup D a := by
    intro hmem
    rcases (S.mem_line_iff hdD ha had.symm hxD).1 hmem with h | h | h
    · exact hxa (h ▸ had.symm)
    · exact hxa (h ▸ Commute.refl a)
    · exact hxa (h ▸ (had.symm.mul_left (Commute.refl a)))
  have hdxD : d * x ∈ D := S.mul_mem_of_commute hdD hxD hdx (Ne.symm hxd)
  have hdaD : d * a ∈ D := by rwa [← had.eq]
  have hcard := hL.card_nCore_inf_eq hdD ha had.symm hdaD
    (by rw [S.sing d hdD]; exact Ne.symm hda) hxD hdx hdxD hxT
  rw [hkd, lineN₀_comm] at hcard
  set μ := Nat.card (nCore D a)
  set ν := Nat.card (lineN₀ D a d)
  set ζ := Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G))
  have hdM : d ∈ nCore D a := S.mem_nCore ha hdD had.symm
  obtain ⟨y, hyD, hay, hya, hyd⟩ := S.exists_not_commute ha hdD had hda hk2
  have hidx : μ ≤ 2 * Nat.card ↥(nCore D a ⊓ Subgroup.centralizer {d}) :=
    S.card_le_two_mul_card_inf_centralizer ha le_rfl (S.mem_nCore ha hyD hay.symm) hdM
      (fun h => hyd h.symm)
  have hμ : μ ≤ 2 ^ (n + 1) * ν := by
    rw [hcard, hn, Nat.add_sub_cancel] at hidx
    calc μ ≤ 2 * (ν * 2 ^ n) := hidx
      _ = 2 ^ (n + 1) * ν := by ring
  have hiso : ν * ν ≤ μ * ζ := S.card_mul_card_le ha (lineN₀ D a d) inf_le_left
    fun u hu v hv => S.commute_of_mem_lineN₀ ha hdD hda hu hv
  have hchain : 2 ^ (k - 1) * ζ ≤ μ := S.two_pow_mul_card_center_le ha
  have hν : 0 < ν := Nat.card_pos
  have hk1 : k - 1 = 2 ^ n := by omega
  have key : 2 ^ (2 ^ n) * (ν * ν) ≤ 2 ^ (2 * n + 2) * (ν * ν) := by
    calc 2 ^ (2 ^ n) * (ν * ν) ≤ 2 ^ (2 ^ n) * (μ * ζ) := Nat.mul_le_mul_left _ hiso
      _ = μ * (2 ^ (k - 1) * ζ) := by rw [hk1]; ring
      _ ≤ μ * μ := Nat.mul_le_mul_left _ hchain
      _ ≤ (2 ^ (n + 1) * ν) * (2 ^ (n + 1) * ν) := Nat.mul_le_mul hμ hμ
      _ = 2 ^ (2 * n + 2) * (ν * ν) := by ring
  have hpow : 2 ^ (2 ^ n) ≤ 2 ^ (2 * n + 2) := Nat.le_of_mul_le_mul_right key (by positivity)
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow
  have := two_mul_add_two_lt_two_pow (show 4 ≤ n by omega)
  omega

end CFSG.Timmesfeld.Bridge
