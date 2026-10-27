module

public import CFSG.RankThree.PartOne.SLBN.LocalCyclic
public import CFSG.RankThree.PartOne.SLBN.SL2Cover
public import CFSG.RankThree.PartOne.SRC.ProductCover

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup Matrix CFSG
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem ker_le_center_prod_nine (hK : Nat.card K = 9) [CharP K 3] {W : Type} [Group W] [Finite W]
    [Group.IsPerfect W] (ρ : W →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 3 ρ.ker) (hmin : ∀ M : Subgroup W, M.map ρ = ⊤ → M = ⊤)
    (hrank : ∀ E : Subgroup W, IsElementaryAbelian 3 E → Nat.card E ≤ 27) :
    ρ.ker ≤ Subgroup.center W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hQ : CFSG.IsQuasisimple (SL(2, K)) := sl2_quasisimple_nine hK
  obtain ⟨m₁, hm₁2, hm₁, hm₁g⟩ := CFSG.RankThree.PartOne.SRC.bigAt_of_card (p := 3) (e := 2) hp2
    le_rfl (F := K) (by rw [hK]; norm_num)
  obtain ⟨n₁, hn₁⟩ := CFSG.RankThree.PartOne.SRC.card_center_SL2_eq_two_pow K
  have hp4 : Nat.Coprime (3 ^ 4) 2 := by norm_num
  have hp4SL : 3 ^ 4 ∣ Nat.card (SL(2, K)) * Nat.card (SL(2, K)) := by
    rw [card_sl2_nine hK]; norm_num
  refine CFSG.RankThree.PartOne.SRC.central_of_rank_le_three_gen Nat.prime_three hp2 ρ hρ hker
    hmin ?_ ?_ (fun E hE => by simpa using hrank E hE)
  · intro N hN n hn hdvd
    rw [Nat.card_prod] at hdvd
    exact CFSG.RankThree.PartOne.SRC.eq_top_of_card_dvd_prod hQ hQ (m := 3 ^ 4) hp4SL
      (by rw [hn₁, ← pow_add]; exact Nat.Coprime.pow_right _ hp4)
      (fun h => CFSG.RankThree.PartOne.SRC.not_pow_four_dvd_card_GL hn h)
      hm₁ (by rw [hn₁]; exact Nat.Coprime.pow_right _ hm₁2) (hm₁g n hn)
      hm₁ (by rw [hn₁]; exact Nat.Coprime.pow_right _ hm₁2) (hm₁g n hn) N hdvd
  · intro N hN hall
    obtain ⟨ζ, hζ, hζo⟩ := CFSG.RankThree.PartOne.SRC.exists_torus_gen (F := K) 3 2 hp2 le_rfl
      (by rw [hK]; norm_num)
    exact CFSG.RankThree.PartOne.SRC.eq_top_of_coprime_elements hQ hQ
      (CFSG.RankThree.PartOne.SRC.torus_not_mem_center hζ)
      (Nat.Coprime.coprime_dvd_left (CFSG.RankThree.PartOne.SRC.orderOf_torus_dvd ζ) hζo)
      (CFSG.RankThree.PartOne.SRC.torus_not_mem_center hζ)
      (Nat.Coprime.coprime_dvd_left (CFSG.RankThree.PartOne.SRC.orderOf_torus_dvd ζ) hζo) N hall

theorem exists_perfect_cover {P X : Type*} [Group P] [Finite P] [Group X] (ρ : P →* X)
    (W₀ : Subgroup P) (Xi : Subgroup X) (hXi : Xi ≤ W₀.map ρ) (hperf : ⁅Xi, Xi⁆ = Xi) :
    ∃ A : Subgroup P, A ≤ W₀ ∧ A.map ρ = Xi ∧ ⁅A, A⁆ = A := by
  have hstart : (W₀ ⊓ Xi.comap ρ).map ρ = Xi := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := hXi hx
      exact ⟨w, ⟨hw, hx⟩, rfl⟩
  obtain ⟨A, -, hAmin⟩ := Finite.exists_le_minimal
    (p := fun M : Subgroup P => M ≤ W₀ ∧ M.map ρ = Xi) (a := W₀ ⊓ Xi.comap ρ)
    ⟨inf_le_left, hstart⟩
  refine ⟨A, hAmin.prop.1, hAmin.prop.2, ?_⟩
  have hle : ⁅A, A⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
  refine le_antisymm hle ?_
  refine hAmin.le_of_le ⟨hle.trans hAmin.prop.1, ?_⟩ hle
  rw [Subgroup.map_commutator, hAmin.prop.2, hperf]

theorem component_of_cover (hK : Nat.card K = 9) [CharP K 3] {P : Type} [Group P] [Finite P]
    (ρ : P →* SL(2, K) × SL(2, K)) (hker : IsPGroup 3 ρ.ker) (W₀ : Subgroup P)
    (hW₀ : ∀ x, x ∈ W₀.map ρ)
    (hcen : ∀ z ∈ W₀, ρ z = 1 → ∀ w ∈ W₀, z * w = w * z)
    (inc : SL(2, K) →* SL(2, K) × SL(2, K)) (pr : SL(2, K) × SL(2, K) →* SL(2, K))
    (hpr : ∀ s, pr (inc s) = s) (hrange : ∀ x ∈ inc.range, inc (pr x) = x) :
    ∃ A : Subgroup P, A ≤ W₀ ∧ (∀ a ∈ A, ρ a ∈ inc.range) ∧ Comp P A ∧
      ∃ e ∈ A, e ^ 3 = 1 ∧ ρ e ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : CFSG.IsQuasisimple (SL(2, K)) := sl2_quasisimple_nine hK
  have hperf : ⁅inc.range, inc.range⁆ = inc.range := by
    have h1 := hQ.1.commutator_eq_top
    rw [_root_.commutator_def] at h1
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]
  obtain ⟨A, hAW, hAmap, hAperf⟩ := exists_perfect_cover ρ W₀ inc.range (fun x _ => hW₀ x) hperf
  let ρA : A →* SL(2, K) := pr.comp (ρ.comp A.subtype)
  have hρA : ∀ a : A, ρA a = pr (ρ a) := fun a => rfl
  have hAin : ∀ a : A, ρ a ∈ inc.range := fun a => hAmap ▸ Subgroup.mem_map_of_mem ρ a.2
  have hsurj : Function.Surjective ρA := by
    intro s
    have : inc s ∈ A.map ρ := hAmap ▸ ⟨s, rfl⟩
    obtain ⟨a, ha, hρa⟩ := this
    exact ⟨⟨a, ha⟩, by rw [hρA]; change pr (ρ a) = s; rw [hρa, hpr]⟩
  have hker1 : ∀ a : A, ρA a = 1 → ρ a = 1 := by
    intro a h
    have := hrange _ (hAin a)
    rw [hρA] at h
    rw [h, map_one] at this
    exact this.symm
  have hkerA : IsPGroup 3 ρA.ker := by
    intro x
    have hx1 : ρ ((x : A) : P) = 1 := hker1 x x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : A) : P), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : P)) hk))⟩
  have hcenA : ρA.ker ≤ Subgroup.center A := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subtype.ext ((hcen (x : P) (hAW x.2) (hker1 x hx) (g : P) (hAW g.2)).symm))
  have hAperf' : Group.IsPerfect A := Subgroup.isPerfect_iff.mpr hAperf
  refine ⟨A, hAW, fun a ha => hAin ⟨a, ha⟩, ⟨hAperf', ?_, ?_⟩, ?_⟩
  · intro N hN
    exact normal_le_center_or_top_nine ρA hK hsurj hkerA hcenA N
  · exact exists_five_noncentral_nine ρA hK hsurj hkerA
  · obtain ⟨e, he3, heρ⟩ := exists_pow_three_eq_one_nine ρA hK hsurj hkerA hcenA
    refine ⟨(e : P), e.2, congrArg Subtype.val he3 |>.trans rfl, fun h => heρ ?_⟩
    rw [hρA]
    rw [h, map_one]

theorem isCyclic_ker_of_cover_sl2_sq (hK : Nat.card K = 9) [CharP K 3] {P : Type} [Group P]
    [Finite P] (ρ : P →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 3 ρ.ker)
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 3 E → Nat.card E ≤ 27) : IsCyclic ρ.ker := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : CFSG.IsQuasisimple (SL(2, K)) := sl2_quasisimple_nine hK
  have hXperf : Group.IsPerfect (SL(2, K) × SL(2, K)) :=
    CFSG.RankThree.PartOne.SRC.isPerfect_prod hQ.1 hQ.1
  obtain ⟨W₀, -, hW₀min⟩ := Finite.exists_le_minimal
    (p := fun M : Subgroup P => M.map ρ = ⊤) (a := ⊤) (by rw [Subgroup.map_top_of_surjective ρ hρ])
  set ρ₀ : W₀ →* SL(2, K) × SL(2, K) := ρ.comp W₀.subtype with hρ₀
  have hρ₀s : Function.Surjective ρ₀ := by
    intro x
    have hx : x ∈ W₀.map ρ := by
      rw [hW₀min.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin₀ : ∀ M : Subgroup W₀, M.map ρ₀ = ⊤ → M = ⊤ := by
    intro M hM
    have h1 : (M.map W₀.subtype).map ρ = ⊤ := by
      rw [Subgroup.map_map]
      exact hM
    have h2 := hW₀min.le_of_le h1 (Subgroup.map_subtype_le M)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  have hker₀ : IsPGroup 3 ρ₀.ker := by
    intro x
    have hx1 : ρ ((x : W₀) : P) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : W₀) : P), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : P)) hk))⟩
  have hperf : Group.IsPerfect W₀ := by
    rw [Group.isPerfect_def]
    apply hmin₀
    have h1 := hXperf.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hρ₀s]
    rwa [_root_.commutator_def] at h1
  have hrank₀ : ∀ E : Subgroup W₀, IsElementaryAbelian 3 E → Nat.card E ≤ 27 := by
    intro E hE
    have := hrank (E.map W₀.subtype)
      (CFSG.RankThree.PartOne.SRC.isElementaryAbelian_map' W₀.subtype hE)
    rwa [Subgroup.card_map_of_injective W₀.subtype_injective] at this
  have hcen₀ := ker_le_center_prod_nine hK ρ₀ hρ₀s hker₀ hmin₀ hrank₀
  have hcen : ∀ z ∈ W₀, ρ z = 1 → ∀ w ∈ W₀, z * w = w * z := by
    intro z hz hρz w hw
    have hzk : (⟨z, hz⟩ : W₀) ∈ ρ₀.ker := hρz
    have := Subgroup.mem_center_iff.mp (hcen₀ hzk) ⟨w, hw⟩
    exact (congrArg Subtype.val this).symm
  have hW₀top : ∀ x, x ∈ W₀.map ρ := fun x => by rw [hW₀min.prop]; exact mem_top x
  obtain ⟨A₁, hA₁W, hA₁in, hA₁c, e₁, he₁A, he₁3, he₁ρ⟩ := component_of_cover hK ρ hker W₀ hW₀top
    hcen (MonoidHom.inl _ _) (MonoidHom.fst _ _) (fun s => rfl)
    (fun x ⟨s, hs⟩ => by rw [← hs]; rfl)
  obtain ⟨A₂, hA₂W, hA₂in, hA₂c, e₂, he₂A, he₂3, he₂ρ⟩ := component_of_cover hK ρ hker W₀ hW₀top
    hcen (MonoidHom.inr _ _) (MonoidHom.snd _ _) (fun s => rfl)
    (fun x ⟨s, hs⟩ => by rw [← hs]; rfl)
  have hA₁perf : ⁅A₁, A₁⁆ = A₁ := Subgroup.isPerfect_iff.mp hA₁c.perfect
  have hT : ⁅A₁, A₂⁆ ≤ W₀ ⊓ ρ.ker := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact W₀.mul_mem (W₀.mul_mem (W₀.mul_mem (hA₁W ha) (hA₂W hb)) (W₀.inv_mem (hA₁W ha)))
        (W₀.inv_mem (hA₂W hb))
    · obtain ⟨s, hs⟩ := hA₁in a ha
      obtain ⟨s', hs'⟩ := hA₂in b hb
      show ρ ⁅a, b⁆ = 1
      rw [map_commutatorElement, ← hs, ← hs']
      refine Prod.ext ?_ ?_ <;> simp [commutatorElement_def]
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := by
    refine commute_of_commutator_commutator_eq_bot hA₁perf ?_
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro z hz x hx
    rw [Subgroup.mem_bot]
    have hzT := hT hz
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hcen z hzT.1 (MonoidHom.mem_ker.mp hzT.2) x (hA₁W hx))
  have hdisj : ∀ x ∈ A₁, ∀ y ∈ A₂, ρ x = ρ y → ρ x ^ 2 = 1 := by
    intro x hx y hy hxy
    obtain ⟨s, hs⟩ := hA₁in x hx
    obtain ⟨s', hs'⟩ := hA₂in y hy
    have h1 : (s, (1 : SL(2, K))) = (1, s') := by
      have := hs.trans (hxy.trans hs'.symm)
      exact this
    have hs1 : s = 1 := (Prod.ext_iff.mp h1).1
    rw [← hs, hs1]
    simp
  exact isCyclic_of_local ρ ρ.ker hker le_rfl hrank hA₁c hA₂c hcomm
    ⟨e₁, he₁A, he₁3, he₁ρ⟩ ⟨e₂, he₂A, he₂3, he₂ρ⟩ hdisj

end CFSG.RankThree.PartOne.SLBN
