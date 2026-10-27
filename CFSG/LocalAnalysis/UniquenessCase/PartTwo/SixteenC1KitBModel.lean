module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitBClass
public import CFSG.Sporadic.Co2Smith.OrbitIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] Multiplicative.mul Multiplicative.semigroup Multiplicative.commSemigroup
attribute [-instance] Multiplicative.mulOneClass Multiplicative.monoid Multiplicative.commMonoid
attribute [-instance] Multiplicative.divInvMonoid Multiplicative.divisionMonoid
attribute [-instance] Multiplicative.divisionCommMonoid Multiplicative.group

theorem s16c1b_aSet_conj {W : Type} [CommGroup W] {X : Subgroup (MulAut W)} {h : MulAut W}
    (hh : h ∈ X) {A : Subgroup (MulAut W)} :
    A.map (MulAut.conj h).toMonoidHom ∈ E3.aSet 2 X ↔ A ∈ E3.aSet 2 X := by
  let c : MulAut W →* MulAut W := (MulAut.conj h).toMonoidHom
  let c' : MulAut W →* MulAut W := (MulAut.conj h⁻¹).toMonoidHom
  have hc_inj : Function.Injective c := (MulAut.conj h).injective
  have hc'c : c.comp c' = MonoidHom.id (MulAut W) := by
    ext x; simp [c, c', MulAut.conj_apply, mul_assoc]
  have hcc' : c'.comp c = MonoidHom.id (MulAut W) := by
    ext x; simp [c, c', MulAut.conj_apply, mul_assoc]
  have hXc : X.map c = X := by
    apply le_antisymm
    · rintro - ⟨x, hx, rfl⟩
      exact X.mul_mem (X.mul_mem hh hx) (X.inv_mem hh)
    · intro x hx
      refine ⟨h⁻¹ * x * h, X.mul_mem (X.mul_mem (X.inv_mem hh) hx) hh, ?_⟩
      show h * (h⁻¹ * x * h) * h⁻¹ = x
      group
  have hmq : ∀ P Q : Subgroup (MulAut W), E3.mQuot (P.map c) (Q.map c) = E3.mQuot P Q := by
    intro P Q
    unfold E3.mQuot
    rw [Subgroup.relIndex_map_map_of_injective (f := c) Q P hc_inj]
  constructor
  · intro hA'
    rw [E3.aSet] at hA' ⊢
    simp only [Set.mem_setOf_eq] at hA' ⊢
    obtain ⟨hle, hne, hel, hfix⟩ := hA'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      have h1 : c a ∈ A.map c := Subgroup.mem_map_of_mem c ha
      have h2 : c a ∈ X := hle h1
      have : a = h⁻¹ * (h * a * h⁻¹) * h := by group
      rw [this]
      exact X.mul_mem (X.mul_mem (X.inv_mem hh) h2) hh
    · intro hbot
      apply hne
      rw [hbot, Subgroup.map_bot]
    · refine ⟨?_, ?_⟩
      · intro a ha b hb
        apply hc_inj
        have h1 : c (a * b) = c (b * a) := by
          rw [map_mul, map_mul]
          exact hel.1 (c a) (Subgroup.mem_map_of_mem c ha) (c b) (Subgroup.mem_map_of_mem c hb)
        exact h1
      · intro a ha
        apply hc_inj
        have h1 : c (a ^ 2) = c 1 := by
          rw [map_pow, map_one]
          exact hel.2 (c a) (Subgroup.mem_map_of_mem c ha)
        exact h1
    · intro B hBA hm
      have hB' : B.map c ≤ A.map c := Subgroup.map_mono hBA
      have hm' : E3.mQuot (A.map c) (B.map c) < 2 := by rw [hmq]; exact hm
      have hf := hfix (B.map c) hB' hm'
      rw [fixV_map_conj_eq B h, fixV_map_conj_eq A h] at hf
      exact (Subgroup.map_injective h.injective) hf
  · intro hA
    rw [E3.aSet] at hA ⊢
    simp only [Set.mem_setOf_eq] at hA ⊢
    obtain ⟨hle, hne, hel, hfix⟩ := hA
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hXc]
      exact Subgroup.map_mono hle
    · intro hbot
      exact hne ((Subgroup.map_eq_bot_iff_of_injective A hc_inj).mp hbot)
    · refine ⟨?_, ?_⟩
      · rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hel.1 a ha b hb]
      · rintro - ⟨a, ha, rfl⟩
        rw [← map_pow, hel.2 a ha, map_one]
    · intro B' hB' hm'
      let B : Subgroup (MulAut W) := B'.map c'
      have hBA : B ≤ A := by
        calc B = B'.map c' := rfl
          _ ≤ (A.map c).map c' := Subgroup.map_mono hB'
          _ = A.map (c'.comp c) := Subgroup.map_map A c' c
          _ = A.map (MonoidHom.id _) := by rw [hcc']
          _ = A := Subgroup.map_id A
      have hB'eq : B.map c = B' := by
        calc B.map c = (B'.map c').map c := rfl
          _ = B'.map (c.comp c') := Subgroup.map_map B' c c'
          _ = B'.map (MonoidHom.id _) := by rw [hc'c]
          _ = B' := Subgroup.map_id B'
      have hm : E3.mQuot A B < 2 := by
        have h2 := hm'
        rw [← hB'eq] at h2
        rwa [hmq A B] at h2
      have hf := hfix B hBA hm
      rw [← hB'eq, fixV_map_conj_eq B h, fixV_map_conj_eq A h, hf]

theorem s16c1b_card_ptCent_conj {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    {h : MulAut W} (hh : h ∈ X) (w : W) :
    Nat.card (ptCent X (h⁻¹ w)) = Nat.card (ptCent X w) := by
  have hpt : ptCent X (h⁻¹ w) = (ptCent X w).map (MulAut.conj h⁻¹).toMonoidHom := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxX, hxw⟩ := Subgroup.mem_inf.mp hx
      rw [MulAction.mem_stabilizer_iff] at hxw
      change x (h⁻¹ w) = h⁻¹ w at hxw
      refine Subgroup.mem_map.mpr ⟨MulAut.conj h x, ?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact X.mul_mem (X.mul_mem hh hxX) (X.inv_mem hh)
        · rw [MulAction.mem_stabilizer_iff]
          show (h * x * h⁻¹) w = w
          calc (h * x * h⁻¹) w = h (x (h⁻¹ w)) := rfl
            _ = h (h⁻¹ w) := by rw [hxw]
            _ = w := by simp
      · show (MulAut.conj h⁻¹) ((MulAut.conj h) x) = x
        simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyX, hyw⟩ := Subgroup.mem_inf.mp hy
      rw [MulAction.mem_stabilizer_iff] at hyw
      change y w = w at hyw
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact X.mul_mem (X.mul_mem (X.inv_mem hh) hyX) hh
      · rw [MulAction.mem_stabilizer_iff]
        show (h⁻¹ * y * h) (h⁻¹ w) = h⁻¹ w
        calc (h⁻¹ * y * h) (h⁻¹ w) = h⁻¹ (y (h (h⁻¹ w))) := rfl
          _ = h⁻¹ (y w) := by simp
          _ = h⁻¹ w := by rw [hyw]
  rw [hpt]
  exact Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective

theorem s16c1b_relIndex_ptCent_conj {W : Type} [CommGroup W] (S : Subgroup (MulAut W))
    (h : MulAut W) (w : W) :
    (ptCent (S.map (MulAut.conj h).toMonoidHom) w).relIndex (S.map (MulAut.conj h).toMonoidHom) =
      (ptCent S (h⁻¹ w)).relIndex S := by
  let c : MulAut W →* MulAut W := (MulAut.conj h).toMonoidHom
  have hc_inj : Function.Injective c := (MulAut.conj h).injective
  have hpt : ptCent (S.map c) w = (ptCent S (h⁻¹ w)).map c := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hxw⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hxS
      rw [MulAction.mem_stabilizer_iff] at hxw
      change (MulAut.conj h) y • w = w at hxw
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hyS, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      show y (h⁻¹ w) = h⁻¹ w
      apply h.injective
      calc h (y (h⁻¹ w)) = (h * y * h⁻¹) w := rfl
        _ = w := hxw
        _ = h (h⁻¹ w) := by simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyS, hyw⟩ := Subgroup.mem_inf.mp hy
      rw [MulAction.mem_stabilizer_iff] at hyw
      change y (h⁻¹ w) = h⁻¹ w at hyw
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem c hyS, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      show (h * y * h⁻¹) w = w
      calc (h * y * h⁻¹) w = h (y (h⁻¹ w)) := rfl
        _ = h (h⁻¹ w) := by rw [hyw]
        _ = w := by simp
  rw [hpt]
  exact Subgroup.relIndex_map_map_of_injective (f := c) (ptCent S (h⁻¹ w)) S hc_inj

private theorem s16c1b_map_conj_inv_map_conj {W : Type} [CommGroup W]
    (H : Subgroup (MulAut W)) (h : MulAut W) :
    (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = H := by
  let c : MulAut W →* MulAut W := (MulAut.conj h).toMonoidHom
  let c' : MulAut W →* MulAut W := (MulAut.conj h⁻¹).toMonoidHom
  have hc'c : c'.comp c = MonoidHom.id (MulAut W) := by
    ext x; simp [c, c', MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_map H c' c, hc'c, Subgroup.map_id]

private theorem s16c1b_map_conj_map_conj_inv {W : Type} [CommGroup W]
    (H : Subgroup (MulAut W)) (h : MulAut W) :
    (H.map (MulAut.conj h⁻¹).toMonoidHom).map (MulAut.conj h).toMonoidHom = H := by
  let c : MulAut W →* MulAut W := (MulAut.conj h).toMonoidHom
  let c' : MulAut W →* MulAut W := (MulAut.conj h⁻¹).toMonoidHom
  have hcc' : c.comp c' = MonoidHom.id (MulAut W) := by
    ext x; simp [c, c', MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_map H c c', hcc', Subgroup.map_id]

private theorem s16c1b_exists_vec (u : V₀) : ∃ n : ℕ, n < 64 ∧ vec n = u := by
  have h : ∀ u : V₀, ∃ n : Fin 64, vec (n : ℕ) = u := by decide +kernel
  obtain ⟨n, hn⟩ := h u
  exact ⟨n, n.isLt, hn⟩

private theorem s16c1b_act_vec {g : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hg : HasCode (g : V₀ →ₗ[ZMod 2] V₀) m) (n : ℕ) :
    g (vec n) = vec (act m n) := by
  calc g (vec n) = (LinearMap.toMatrix' (g : V₀ →ₗ[ZMod 2] V₀)).mulVec (vec n) :=
        (LinearMap.toMatrix'_mulVec _ _).symm
    _ = (mat m).mulVec (vec n) := by rw [hg]
    _ = vec (act m n) := (vec_act m n).symm

private theorem s16c1b_vec_inj {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : vec a = vec b) :
    a = b := by
  have hall : ∀ a b : Fin 64, vec (a : ℕ) = vec (b : ℕ) → a = b := by decide +kernel
  have := hall ⟨a, ha⟩ ⟨b, hb⟩ h
  simpa using congrArg Fin.val this

private theorem s16c1b_vec_zero : vec 0 = (0 : V₀) := by decide +kernel

private theorem s16c1b_nodup_eraseDups {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.Nodup.cons ?_ (s16c1b_nodup_eraseDups (as.filter fun b => !b == a))
    intro hmem
    rw [List.mem_eraseDups, List.mem_filter] at hmem
    obtain ⟨-, hba⟩ := hmem
    simp at hba
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem s16c1b_fix_SM {A : Subgroup (MulAut (Multiplicative V₀))}
    (hA : A ∈ E3.aSet 2 s16c1b_ΩM) (hAS : A ≤ s16c1b_SM) {w : Multiplicative V₀} (hw : w ≠ 1)
    (h960 : Nat.card (ptCent s16c1b_ΩM w) = 960)
    (horb : (ptCent s16c1b_SM w).relIndex s16c1b_SM ≤ 4) : ∀ a ∈ A, a w = w := by
  obtain ⟨i, rfl⟩ := s16c1b_classify hA hAS
  intro a ha
  obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨c, hc, hgc⟩ := hgA
  obtain ⟨n, hn64, hn⟩ := s16c1b_exists_vec (Multiplicative.toAdd w)
  have hwn : w = Multiplicative.ofAdd (vec n) := by
    rw [hn]
    simp
  have hq0 : qModel true (Multiplicative.toAdd w) = 0 :=
    (s16c1b_card_ptCent_eq_960_iff hw).mp h960
  have hqB : qB true n = false := by
    have h := qModel_vec true n
    rw [hn, hq0] at h
    cases hb : qB true n with
    | false => rfl
    | true => rw [hb] at h; exact absurd h (by decide)
  have horbSize : s16c1b_orbSize n ≤ 4 := by
    let l : List ℕ := (s16c1b_S0.map (fun c => act c n)).eraseDups
    have hl_len : l.length = s16c1b_orbSize n := rfl
    have hl_lt : ∀ m ∈ l, m < 64 := by
      intro m hm
      rw [List.mem_eraseDups] at hm
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
      exact act_lt c n
    let pts : Fin l.length → Multiplicative V₀ := fun j => Multiplicative.ofAdd (vec (l.get j))
    have hln : l.Nodup := s16c1b_nodup_eraseDups (s16c1b_S0.map (fun c => act c n))
    have hpts_inj : Function.Injective pts := by
      intro j k hjk
      have h1 : l.get j = l.get k :=
        s16c1b_vec_inj (hl_lt _ (l.get_mem j)) (hl_lt _ (l.get_mem k))
          (Multiplicative.ofAdd.injective hjk)
      exact List.Nodup.get_inj_iff hln |>.mp h1
    have hpts_mem : ∀ j, pts j ∈ MulAction.orbit s16c1b_SM w := by
      intro j
      have hj : l.get j ∈ s16c1b_S0.map (fun c => act c n) := by
        rw [← List.mem_eraseDups]
        exact l.get_mem j
      obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hj
      obtain ⟨g, hgS, hgcode⟩ := s16c1b_S₀_spec.2.2.2 c hc
      refine MulAction.mem_orbit_iff.mpr ⟨⟨s16c1b_κ g, ?_⟩, ?_⟩
      · exact Subgroup.mem_map_of_mem s16c1b_κ hgS
      · show s16c1b_κ g w = pts j
        rw [hwn, s16c1b_κ_apply, s16c1b_act_vec hgcode.1 n, hcn]
    have hbound : l.length ≤ 4 := by
      have h1 := CFSG.Sporadic.Co2Smith.le_relIndex_of_orbit (T := s16c1b_SM)
        (F := s16c1b_SM) le_rfl w pts hpts_inj hpts_mem
      have h2 : (s16c1b_SM ⊓ MulAction.stabilizer (MulAut (Multiplicative V₀)) w).relIndex
          s16c1b_SM ≤ 4 := horb
      exact le_trans h1 h2
    rwa [hl_len] at hbound
  have horb' : ¬ (4 < s16c1b_orbSize n) := by omega
  have hn0 : n ≠ 0 := by
    intro h0
    apply hw
    rw [hwn, h0]
    simp [s16c1b_vec_zero]
  have hcheck : s16c1b_A.all (fun a => a.all fun c => act c n == n) = true := by
    have h := s16c1b_checkOrb_ok
    simp only [s16c1b_checkOrb, Bool.and_eq_true, List.all_eq_true] at h
    have h1 := h n (List.mem_range.mpr hn64)
    have hn0' : (n == 0) = false := beq_eq_false_iff_ne.mpr hn0
    have horb'' : decide (4 < s16c1b_orbSize n) = false := by
      rw [decide_eq_false_iff_not]
      exact horb'
    rw [hn0', hqB, horb''] at h1
    simpa using h1
  have hc_fix : act c n = n := by
    have hlen : i.val < s16c1b_A.length := by
      rw [show s16c1b_A.length = 3 from rfl]
      exact i.isLt
    have hmemA : s16c1b_A.getD i.val [] ∈ s16c1b_A := by
      rw [List.getD_eq_get s16c1b_A [] ⟨i.val, hlen⟩]
      exact List.get_mem _ _
    have h1 := List.all_eq_true.mp hcheck (s16c1b_A.getD i.val []) hmemA
    exact beq_iff_eq.mp (List.all_eq_true.mp h1 c hc)
  rw [hwn]
  show s16c1b_κ g (Multiplicative.ofAdd (vec n)) = Multiplicative.ofAdd (vec n)
  rw [s16c1b_κ_apply, s16c1b_act_vec hgc.1 n, hc_fix]

theorem s16c1b_a2Fix_model : OmegaA2Fix s16c1b_ΩM := by
  intro S hS A hA hAS w hw h960 hrel
  obtain ⟨h, hh, rfl⟩ := s16c1b_sylow_conj hS
  let A' : Subgroup (MulAut (Multiplicative V₀)) := A.map (MulAut.conj h⁻¹).toMonoidHom
  have hh_inv : h⁻¹ ∈ s16c1b_ΩM := s16c1b_ΩM.inv_mem hh
  have hA' : A' ∈ E3.aSet 2 s16c1b_ΩM := (s16c1b_aSet_conj hh_inv).2 hA
  have hA'S : A' ≤ s16c1b_SM := by
    calc A' = A.map (MulAut.conj h⁻¹).toMonoidHom := rfl
      _ ≤ (s16c1b_SM.map (MulAut.conj h).toMonoidHom).map
            (MulAut.conj h⁻¹).toMonoidHom := Subgroup.map_mono hAS
      _ = s16c1b_SM := s16c1b_map_conj_inv_map_conj s16c1b_SM h
  have hw' : h⁻¹ w ≠ 1 := by
    intro h1
    apply hw
    calc w = h (h⁻¹ w) := by simp
      _ = h 1 := by rw [h1]
      _ = 1 := by simp
  have h960' : Nat.card (ptCent s16c1b_ΩM (h⁻¹ w)) = 960 :=
    (s16c1b_card_ptCent_conj hh w).trans h960
  have hrel' : (ptCent s16c1b_SM (h⁻¹ w)).relIndex s16c1b_SM ≤ 4 :=
    (s16c1b_relIndex_ptCent_conj s16c1b_SM h w).symm.trans_le hrel
  have hfix := s16c1b_fix_SM hA' hA'S hw' h960' hrel'
  intro a ha
  have hAeq : A'.map (MulAut.conj h).toMonoidHom = A := s16c1b_map_conj_map_conj_inv A h
  have haA' : a ∈ A'.map (MulAut.conj h).toMonoidHom := by rwa [hAeq]
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp haA'
  show h (a' (h⁻¹ w)) = w
  rw [hfix a' ha']
  simp

private theorem s16c1b_okWord_omega {e : List ℕ} (hok : s16c1b_okWord e = true) :
    wordProd e ∈ Ω₀ true := by
  rw [s16c1b_okWord, Bool.and_eq_true] at hok
  exact (wordProd_mem_omegaGroup_iff (fun n hn => List.all_eq_true.mp hok.1 n hn)).mpr
    (Nat.even_iff.mpr (beq_iff_eq.mp hok.2))

private noncomputable def s16c1b_E : Subgroup (MulAut (Multiplicative V₀)) :=
  Subgroup.closure {s16c1b_κ (wordProd [49,3]), s16c1b_κ (wordProd [56,48,31,12])}

private theorem s16c1b_g1_cube_code :
    mul (mul (wordC [49,3]) (wordC [49,3])) (wordC [49,3]) = one := by decide +kernel

private theorem s16c1b_g2_cube_code :
    mul (mul (wordC [56,48,31,12]) (wordC [56,48,31,12])) (wordC [56,48,31,12]) = one := by
  decide +kernel

private theorem s16c1b_g1_g2_comm_code :
    mul (wordC [49,3]) (wordC [56,48,31,12]) =
      mul (wordC [56,48,31,12]) (wordC [49,3]) := by decide +kernel

private theorem s16c1b_g1_ne_one_code : wordC [49,3] ≠ one := by decide +kernel

private theorem s16c1b_g2_ne_one_code : wordC [56,48,31,12] ≠ one := by decide +kernel

private theorem s16c1b_g2_ne_g1_code : wordC [56,48,31,12] ≠ wordC [49,3] := by decide +kernel

private theorem s16c1b_g2_ne_g1sq_code :
    wordC [56,48,31,12] ≠ mul (wordC [49,3]) (wordC [49,3]) := by decide +kernel

private theorem s16c1b_g1_cube : wordProd [49,3] ^ 3 = 1 := by
  have hc : Coded (wordProd [49,3] ^ 3)
      (mul (mul (wordC [49,3]) (wordC [49,3])) (wordC [49,3])) := by
    have h := ((coded_wordProd [49,3]).mul (coded_wordProd [49,3])).mul
      (coded_wordProd [49,3])
    simpa [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two] using h
  rw [s16c1b_g1_cube_code] at hc
  exact (hc.eq_iff coded_one).mpr rfl

private theorem s16c1b_g2_cube : wordProd [56,48,31,12] ^ 3 = 1 := by
  have hc : Coded (wordProd [56,48,31,12] ^ 3)
      (mul (mul (wordC [56,48,31,12]) (wordC [56,48,31,12])) (wordC [56,48,31,12])) := by
    have h := ((coded_wordProd [56,48,31,12]).mul
      (coded_wordProd [56,48,31,12])).mul (coded_wordProd [56,48,31,12])
    simpa [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two] using h
  rw [s16c1b_g2_cube_code] at hc
  exact (hc.eq_iff coded_one).mpr rfl

private theorem s16c1b_kappa_g1_cube : (s16c1b_κ (wordProd [49,3])) ^ 3 = 1 := by
  rw [← map_pow, s16c1b_g1_cube, map_one]

private theorem s16c1b_kappa_g2_cube : (s16c1b_κ (wordProd [56,48,31,12])) ^ 3 = 1 := by
  rw [← map_pow, s16c1b_g2_cube, map_one]

private theorem s16c1b_kappa_comm :
    s16c1b_κ (wordProd [49,3]) * s16c1b_κ (wordProd [56,48,31,12]) =
      s16c1b_κ (wordProd [56,48,31,12]) * s16c1b_κ (wordProd [49,3]) := by
  rw [← map_mul, ← map_mul]
  congr 1
  have h1 : Coded (wordProd [49,3] * wordProd [56,48,31,12])
      (mul (wordC [49,3]) (wordC [56,48,31,12])) :=
    (coded_wordProd [49,3]).mul (coded_wordProd [56,48,31,12])
  have h2 : Coded (wordProd [56,48,31,12] * wordProd [49,3])
      (mul (wordC [56,48,31,12]) (wordC [49,3])) :=
    (coded_wordProd [56,48,31,12]).mul (coded_wordProd [49,3])
  exact (h1.eq_iff h2).mpr s16c1b_g1_g2_comm_code

private theorem s16c1b_kappa_g1_ne_one : s16c1b_κ (wordProd [49,3]) ≠ 1 := by
  intro h
  have hg : wordProd [49,3] = 1 := s16c1b_κ_injective (by rw [h, map_one])
  exact s16c1b_g1_ne_one_code (((coded_wordProd [49,3]).eq_iff coded_one).mp hg)

private theorem s16c1b_kappa_g2_ne_one : s16c1b_κ (wordProd [56,48,31,12]) ≠ 1 := by
  intro h
  have hg : wordProd [56,48,31,12] = 1 := s16c1b_κ_injective (by rw [h, map_one])
  exact s16c1b_g2_ne_one_code (((coded_wordProd [56,48,31,12]).eq_iff coded_one).mp hg)

private theorem s16c1b_kappa_g2_ne_g1 :
    s16c1b_κ (wordProd [56,48,31,12]) ≠ s16c1b_κ (wordProd [49,3]) := by
  intro h
  have hg : wordProd [56,48,31,12] = wordProd [49,3] := s16c1b_κ_injective h
  have h1 : Coded (wordProd [56,48,31,12]) (wordC [56,48,31,12]) := coded_wordProd _
  have h2 : Coded (wordProd [49,3]) (wordC [49,3]) := coded_wordProd _
  exact s16c1b_g2_ne_g1_code ((h1.eq_iff h2).mp hg)

private theorem s16c1b_kappa_g2_ne_g1sq :
    s16c1b_κ (wordProd [56,48,31,12]) ≠ (s16c1b_κ (wordProd [49,3])) ^ 2 := by
  intro h
  rw [← map_pow] at h
  have hg : wordProd [56,48,31,12] = wordProd [49,3] ^ 2 := s16c1b_κ_injective h
  have h1 : Coded (wordProd [56,48,31,12]) (wordC [56,48,31,12]) := coded_wordProd _
  have h2 : Coded (wordProd [49,3] ^ 2) (mul (wordC [49,3]) (wordC [49,3])) := by
    simpa [pow_two] using (coded_wordProd [49,3]).mul (coded_wordProd [49,3])
  exact s16c1b_g2_ne_g1sq_code ((h1.eq_iff h2).mp hg)

private theorem s16c1b_closure_pair {G : Type*} [Group G] [Finite G] [DecidableEq G] {a b : G}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2) :
    IsPGroup 3 (Subgroup.closure ({a, b} : Set G)) ∧
      ¬ IsCyclic (Subgroup.closure ({a, b} : Set G)) := by
  let E := Subgroup.closure ({a, b} : Set G)
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hpair : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab.symm
    · exact absurd rfl hxy
  haveI : IsMulCommutative E := isMulCommutative_closure hpair
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    fun x hx y hy => setLike_mul_comm hx hy
  have h3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ha3
      · exact hb3
    | one => simp
    | mul x y hxE hyE ihx ihy =>
      have hc : Commute x y := hcommE x hxE y hyE
      rw [Commute.mul_pow hc 3, ihx, ihy, one_mul]
    | inv x hxE ihx => rw [inv_pow, ihx, inv_one]
  refine ⟨?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    exact h3 g.1 g.2
  · intro hcyc
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      exact h3 g.1 g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    have hle : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hmem : ∀ x ∈ E, x = 1 ∨ x = g.1 ∨ x = g.1 ^ 2 := by
      intro x hx
      have hxzp : (⟨x, hx⟩ : E) ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top _
      rw [mem_zpowers_iff_mem_range_orderOf] at hxzp
      obtain ⟨n, hnmem, hneq⟩ := Finset.mem_image.mp hxzp
      have hn3 : n < 3 := lt_of_lt_of_le (Finset.mem_range.mp hnmem) hle
      interval_cases n
      · left
        have h' : (⟨x, hx⟩ : E) = 1 := by rw [← hneq, pow_zero]
        exact congrArg Subtype.val h'
      · right; left
        have h' : (⟨x, hx⟩ : E) = g := by rw [← hneq, pow_one]
        exact congrArg Subtype.val h'
      · right; right
        have h' : (⟨x, hx⟩ : E) = g ^ 2 := by rw [← hneq]
        simpa using congrArg Subtype.val h'
    rcases hmem a haE with ha1' | ha_g | ha_g2
    · exact ha1 ha1'
    · rcases hmem b hbE with hb1' | hb_g | hb_g2
      · exact hb1 hb1'
      · exact hba (by rw [hb_g, ← ha_g])
      · exact hba2 (by rw [hb_g2, ← ha_g])
    · have hgeq : g.1 = a ^ 2 := by
        have hg3G : g.1 ^ 3 = 1 := by
          have := h3 g.1 g.2
          simpa using this
        have h1 : (g.1 ^ 2) ^ 2 = g.1 := by
          rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_add, hg3G, one_mul, pow_one]
        exact ((congrArg (fun t => t ^ 2) ha_g2).trans h1).symm
      rcases hmem b hbE with hb1' | hb_g | hb_g2
      · exact hb1 hb1'
      · exact hba2 (by rw [hb_g, hgeq])
      · have h' : g.1 ^ 2 = a := by
          have h1 : (a ^ 2) ^ 2 = a := by
            rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_add, ha3, one_mul, pow_one]
          exact (congrArg (fun t => t ^ 2) hgeq).trans h1
        exact hba (by rw [hb_g2, h'])

private theorem s16c1b_coded_conj {e : List ℕ} {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hx : Coded x c) :
    Coded (MulAut.conj (wordProd e) x) (s16c1b_conjC e c) := by
  rw [MulAut.conj_apply]
  have h1 : Coded (wordProd e) (wordC e) := coded_wordProd e
  have h2 : Coded ((wordProd e)⁻¹) (wordC e.reverse) := by
    rw [wordProd_inv]; exact coded_wordProd e.reverse
  have h := h1.mul (hx.mul h2)
  simpa [s16c1b_conjC, mul_assoc] using h

private theorem s16c1b_A_length' : s16c1b_A.length = 3 := by decide +kernel

private theorem s16c1b_A_entries_S0 :
    s16c1b_A.flatten.all (fun c => s16c1b_S0.contains c) = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨L, hL, hcL⟩ := List.mem_flatten.mp hc
  have h := s16c1b_checkA_ok
  simp only [s16c1b_checkA, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, hinv⟩, -⟩ := h.2 L hL
  exact (hinv c hcL).1

private theorem s16c1b_A0_sub_Q :
    (s16c1b_A.getD 0 []).all (fun c => s16c1b_Q.contains c) = true := by decide +kernel

private theorem s16c1b_A1_sub_Q :
    (s16c1b_A.getD 1 []).all (fun c => s16c1b_Q.contains c) = true := by decide +kernel

private theorem s16c1b_A2_sub_Q :
    (s16c1b_A.getD 2 []).all (fun c => s16c1b_Q.contains c) = true := by decide +kernel

private theorem s16c1b_A_sub_Q (i : Fin 3) :
    (s16c1b_A.getD i.val []).all (fun c => s16c1b_Q.contains c) = true := by
  fin_cases i
  · exact s16c1b_A0_sub_Q
  · exact s16c1b_A1_sub_Q
  · exact s16c1b_A2_sub_Q

private theorem s16c1b_sameSet_A (i : Fin 3) :
    s16c1b_sameSet ((s16c1b_A.getD i.val []).map (s16c1b_conjC [50,3]))
      (s16c1b_A.getD (i + 1).val []) = true := by
  fin_cases i <;> decide +kernel

private theorem s16c1b_sameSet_A_rev (i : Fin 3) :
    s16c1b_sameSet ((s16c1b_A.getD (i + 1).val []).map (s16c1b_conjC [3,50]))
      (s16c1b_A.getD i.val []) = true := by
  fin_cases i <;> decide +kernel

private theorem s16c1b_Q_mul_closed :
    s16c1b_Q.all (fun a => s16c1b_Q.all fun b => s16c1b_Q.contains (mul a b)) = true := by
  decide +kernel

private theorem s16c1b_Q_one_mem : s16c1b_Q.contains one = true := by decide +kernel

private theorem s16c1b_Q_conj_e1 :
    s16c1b_Q.all (fun q => s16c1b_Q.contains (s16c1b_conjC [49,3] q)) = true := by
  decide +kernel

private theorem s16c1b_Q_conj_e1rev :
    s16c1b_Q.all (fun q => s16c1b_Q.contains (s16c1b_conjC [3,49] q)) = true := by
  decide +kernel

private theorem s16c1b_Q_conj_e2 :
    s16c1b_Q.all (fun q => s16c1b_Q.contains (s16c1b_conjC [56,48,31,12] q)) = true := by
  decide +kernel

private theorem s16c1b_Q_conj_e2rev :
    s16c1b_Q.all (fun q => s16c1b_Q.contains (s16c1b_conjC [12,31,48,56] q)) = true := by
  decide +kernel

private theorem s16c1b_Qgen_codes (g : ℕ) (hg : g ∈ s16c1b_A.flatten) :
    ∃ G ∈ s16c1b_Qsub, Coded G g := by
  obtain ⟨L, hL, hgL⟩ := List.mem_flatten.mp hg
  obtain ⟨i, hi, hLi⟩ := List.mem_iff_getElem.mp hL
  have hi3 : i < 3 := by have h := s16c1b_A_length'; omega
  let ii : Fin 3 := ⟨i, hi3⟩
  have hgetD : s16c1b_A.getD ii.val [] = L := by
    rw [List.getD_eq_getElem s16c1b_A [] hi]; exact hLi
  have hgL' : g ∈ s16c1b_A.getD ii.val [] := by rw [hgetD]; exact hgL
  have hgflat : g ∈ s16c1b_A.flatten := List.mem_flatten.mpr ⟨L, hL, hgL⟩
  have hcS0 : s16c1b_S0.contains g = true :=
    List.all_eq_true.mp s16c1b_A_entries_S0 g hgflat
  obtain ⟨G, hG, hGC⟩ := s16c1b_S₀_spec.2.2.2 g (List.contains_iff_mem.mp hcS0)
  exact ⟨G, le_iSup (fun i : Fin 3 => s16c1b_Asub i) ii ⟨g, hgL', hGC⟩, hGC⟩

private noncomputable def s16c1b_QcodesSub : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) where
  carrier := {g | ∃ c ∈ s16c1b_Q, Coded g c}
  one_mem' := ⟨one, List.contains_iff_mem.mp s16c1b_Q_one_mem, coded_one⟩
  mul_mem' := by
    rintro g h ⟨c, hc, hgc⟩ ⟨d, hd, hhd⟩
    refine ⟨mul c d, ?_, hgc.mul hhd⟩
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp (List.all_eq_true.mp s16c1b_Q_mul_closed c hc) d hd)
  inv_mem' := by
    haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) :=
      Finite.of_injective (fun f : V₀ ≃ₗ[ZMod 2] V₀ => (f : V₀ → V₀))
        (fun f g h => LinearEquiv.ext (congrFun h))
    rintro g ⟨c, hc, hgc⟩
    have hpow : ∀ n : ℕ, ∃ d ∈ s16c1b_Q, Coded (g ^ n) d := by
      intro n
      induction n with
      | zero =>
        exact ⟨one, List.contains_iff_mem.mp s16c1b_Q_one_mem, by simpa using coded_one⟩
      | succ n ih =>
        obtain ⟨d, hd, hgd⟩ := ih
        refine ⟨mul d c, ?_, ?_⟩
        · exact List.contains_iff_mem.mp
            (List.all_eq_true.mp (List.all_eq_true.mp s16c1b_Q_mul_closed d hd) c hc)
        · rw [pow_succ]; exact hgd.mul hgc
    obtain ⟨d, hd, hgd⟩ := hpow (orderOf g - 1)
    have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
    have hpos : 0 < orderOf g := hfin.orderOf_pos
    have hmul : g ^ (orderOf g - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ orderOf g), pow_orderOf_eq_one]
    have hinv : g ^ (orderOf g - 1) = g⁻¹ := eq_inv_of_mul_eq_one_left hmul
    exact ⟨d, hd, by rwa [hinv] at hgd⟩

private theorem s16c1b_Q_inner {g : ℕ} (hg : ∃ G ∈ s16c1b_Qsub, Coded G g) :
    ∀ (l : List ℕ), (∀ x ∈ l, ∃ G ∈ s16c1b_Qsub, Coded G x) →
      ∀ {acc : List ℕ}, (∀ x ∈ acc, ∃ G ∈ s16c1b_Qsub, Coded G x) →
        ∀ c ∈ l.foldl (fun acc' x =>
          if acc'.contains (Code.mul g x) then acc' else acc' ++ [Code.mul g x]) acc,
          ∃ G ∈ s16c1b_Qsub, Coded G c := by
  intro l
  induction l with
  | nil => intro _ acc hacc c hc; exact hacc c (by simpa using hc)
  | cons x xs ih =>
    intro hl acc hacc c hc
    rw [List.foldl_cons] at hc
    refine ih (fun y hy => hl y (List.mem_cons_of_mem x hy)) ?_ c hc
    by_cases hcont : acc.contains (Code.mul g x)
    · rw [if_pos hcont]; exact hacc
    · rw [if_neg hcont]
      intro y hy
      rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hacc y hy
      · obtain ⟨G, hG, hcG⟩ := hg
        obtain ⟨X, hX, hcX⟩ := hl x List.mem_cons_self
        exact ⟨G * X, s16c1b_Qsub.mul_mem hG hX, hcG.mul hcX⟩

private theorem s16c1b_Q_foldl_gens :
    ∀ (gens : List ℕ), (∀ g ∈ gens, ∃ G ∈ s16c1b_Qsub, Coded G g) →
      ∀ (l : List ℕ), (∀ x ∈ l, ∃ G ∈ s16c1b_Qsub, Coded G x) →
        ∀ {acc : List ℕ}, (∀ x ∈ acc, ∃ G ∈ s16c1b_Qsub, Coded G x) →
          ∀ c ∈ gens.foldl (fun acc g => l.foldl (fun acc' x =>
            if acc'.contains (Code.mul g x) then acc' else acc' ++ [Code.mul g x]) acc) acc,
            ∃ G ∈ s16c1b_Qsub, Coded G c := by
  intro gens
  induction gens with
  | nil =>
    intro _ l _ acc hacc c hc
    exact hacc c (by simpa using hc)
  | cons g gs ih =>
    intro hgens l hl acc hacc c hc
    rw [List.foldl_cons] at hc
    refine ih (fun y hy => hgens y (List.mem_cons_of_mem g hy)) l hl ?_ c hc
    exact s16c1b_Q_inner (hgens g List.mem_cons_self) l hl hacc

private theorem s16c1b_Q_step_subset_codes {l : List ℕ}
    (hl : ∀ x ∈ l, ∃ G ∈ s16c1b_Qsub, Coded G x) :
    ∀ c ∈ s16c1b_step (s16c1b_A.flatten.eraseDups) l, ∃ G ∈ s16c1b_Qsub, Coded G c := by
  unfold s16c1b_step
  exact s16c1b_Q_foldl_gens _ (fun g hg => s16c1b_Qgen_codes g (List.mem_eraseDups.mp hg))
    l hl (fun x hx => hl x hx)

private theorem s16c1b_Q_iter_subset_codes (n : ℕ) :
    ∀ {l : List ℕ}, (∀ x ∈ l, ∃ G ∈ s16c1b_Qsub, Coded G x) →
      ∀ c ∈ s16c1b_iter (s16c1b_A.flatten.eraseDups) n l, ∃ G ∈ s16c1b_Qsub, Coded G c := by
  induction n with
  | zero => intro l hl c hc; exact hl c hc
  | succ n ih => intro l hl c hc; exact ih (s16c1b_Q_step_subset_codes hl) c hc

private theorem s16c1b_QcodesSub_le_Qsub : s16c1b_QcodesSub ≤ s16c1b_Qsub := by
  intro g hg
  obtain ⟨c, hc, hgc⟩ := hg
  obtain ⟨G, hG, hGc⟩ := s16c1b_Q_iter_subset_codes 6 (l := [one])
    (fun x hx => by
      rw [List.mem_singleton] at hx
      exact ⟨1, one_mem s16c1b_Qsub, by rw [hx]; exact coded_one⟩) c hc
  rwa [(hgc.eq_iff hGc).mpr rfl]

private theorem s16c1b_Qsub_le_QcodesSub : s16c1b_Qsub ≤ s16c1b_QcodesSub := by
  refine iSup_le fun i => ?_
  intro g hg
  obtain ⟨c, hc, hgc⟩ := hg
  exact ⟨c, List.contains_iff_mem.mp (List.all_eq_true.mp (s16c1b_A_sub_Q i) c hc), hgc⟩

private theorem s16c1b_map_conj_κ (a : V₀ ≃ₗ[ZMod 2] V₀)
    (A : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) :
    (A.map (MulAut.conj a).toMonoidHom).map s16c1b_κ =
      (A.map s16c1b_κ).map (MulAut.conj (s16c1b_κ a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem s16c1b_Asub_map_conj_le {e : List ℕ} {i j : Fin 3}
    (h : s16c1b_sameSet ((s16c1b_A.getD i.val []).map (s16c1b_conjC e))
      (s16c1b_A.getD j.val []) = true) :
    (s16c1b_Asub i).map (MulAut.conj (wordProd e)).toMonoidHom ≤ s16c1b_Asub j := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨c, hc, hxc⟩ := hx
  have hmem : s16c1b_conjC e c ∈ s16c1b_A.getD j.val [] := by
    have h1 : ((s16c1b_A.getD i.val []).map (s16c1b_conjC e)).all
        (fun q => (s16c1b_A.getD j.val []).contains q) = true :=
      (Bool.and_eq_true_iff.mp h).1
    rw [List.all_map] at h1
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h1 c hc)
  exact ⟨s16c1b_conjC e c, hmem, s16c1b_coded_conj hxc⟩

private theorem s16c1b_wordProd_3_50 : wordProd [3,50] = (wordProd [50,3])⁻¹ := by
  have h1 : Coded (wordProd [3,50]) (wordC [3,50]) := coded_wordProd _
  have h2 : Coded ((wordProd [50,3])⁻¹) (wordC [50,3].reverse) := by
    rw [wordProd_inv]; exact coded_wordProd _
  exact (h1.eq_iff h2).mpr rfl

private theorem s16c1b_Asub_conj_n1 (i : Fin 3) :
    (s16c1b_Asub i).map (MulAut.conj (wordProd [50,3])).toMonoidHom =
      s16c1b_Asub (i + 1) := by
  apply le_antisymm
  · exact s16c1b_Asub_map_conj_le (s16c1b_sameSet_A i)
  · have hrev := s16c1b_Asub_map_conj_le (e := [3,50]) (i := i + 1) (j := i)
      (s16c1b_sameSet_A_rev i)
    have h2 := Subgroup.map_mono (f := (MulAut.conj (wordProd [50,3])).toMonoidHom) hrev
    rw [Subgroup.map_map] at h2
    have hcomp : ((MulAut.conj (wordProd [50,3])).toMonoidHom.comp
        (MulAut.conj (wordProd [3,50])).toMonoidHom) = MonoidHom.id _ := by
      ext x
      rw [s16c1b_wordProd_3_50, map_inv]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hcomp, Subgroup.map_id] at h2

private theorem s16c1b_S0_conj_50_3 :
    s16c1b_S0.all (fun s => s16c1b_S0.contains (s16c1b_conjC [50,3] s)) = true := by
  decide +kernel

private theorem s16c1b_S0_conj_3_50 :
    s16c1b_S0.all (fun s => s16c1b_S0.contains (s16c1b_conjC [3,50] s)) = true := by
  decide +kernel

private theorem s16c1b_SM_map_conj_le {e : List ℕ}
    (h : s16c1b_S0.all (fun s => s16c1b_S0.contains (s16c1b_conjC e s)) = true) :
    s16c1b_SM.map (MulAut.conj (s16c1b_κ (wordProd e))).toMonoidHom ≤ s16c1b_SM := by
  dsimp only [s16c1b_SM]
  rw [← s16c1b_map_conj_κ (wordProd e) s16c1b_S₀]
  apply Subgroup.map_mono
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨c, hc, hgc⟩ := s16c1b_S₀_spec.2.2.1 g hg
  have hcode := s16c1b_coded_conj (e := e) hgc
  have hcq : s16c1b_conjC e c ∈ s16c1b_S0 :=
    List.contains_iff_mem.mp (List.all_eq_true.mp h c hc)
  obtain ⟨g', hg', hg'c⟩ := s16c1b_S₀_spec.2.2.2 (s16c1b_conjC e c) hcq
  have heq : (MulAut.conj (wordProd e)) g = g' := (hcode.eq_iff hg'c).mpr rfl
  change (MulAut.conj (wordProd e)) g ∈ s16c1b_S₀
  rw [heq]
  exact hg'

private theorem s16c1b_SM_mem_conj {e : List ℕ}
    (h : s16c1b_S0.all (fun s => s16c1b_S0.contains (s16c1b_conjC e s)) = true)
    {s : MulAut (Multiplicative V₀)} (hs : s ∈ s16c1b_SM) :
    MulAut.conj (s16c1b_κ (wordProd e)) s ∈ s16c1b_SM :=
  s16c1b_SM_map_conj_le h (Subgroup.mem_map_of_mem _ hs)

private theorem s16c1b_n1_mem_normalizer :
    s16c1b_κ (wordProd [50,3]) ∈
      normalizer (s16c1b_SM : Set (MulAut (Multiplicative V₀))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    exact s16c1b_SM_mem_conj s16c1b_S0_conj_50_3 hs
  · intro hs
    have h := s16c1b_SM_mem_conj s16c1b_S0_conj_3_50 hs
    have hfin : MulAut.conj (s16c1b_κ (wordProd [3,50]))
        (s16c1b_κ (wordProd [50,3]) * s * (s16c1b_κ (wordProd [50,3]))⁻¹) = s := by
      rw [s16c1b_wordProd_3_50, map_inv]
      simp only [MulAut.conj_apply, inv_inv]
      group
    rwa [hfin] at h

private theorem s16c1b_n1_mem :
    s16c1b_κ (wordProd [50,3]) ∈
      normalizer (s16c1b_SM : Set (MulAut (Multiplicative V₀))) ⊓ s16c1b_ΩM :=
  Subgroup.mem_inf.mpr ⟨s16c1b_n1_mem_normalizer,
    Subgroup.mem_map_of_mem _
      (s16c1b_okWord_omega (by decide +kernel : s16c1b_okWord [50,3] = true))⟩

private theorem s16c1b_Qsub_conj {e : List ℕ}
    (h : s16c1b_Q.all (fun q => s16c1b_Q.contains (s16c1b_conjC e q)) = true) :
    (s16c1b_Qsub.map s16c1b_κ).map (MulAut.conj (s16c1b_κ (wordProd e))).toMonoidHom ≤
      s16c1b_Qsub.map s16c1b_κ := by
  rw [← s16c1b_map_conj_κ (wordProd e) s16c1b_Qsub]
  apply Subgroup.map_mono
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨c, hc, hgc⟩ := s16c1b_Qsub_le_QcodesSub hg
  have hcode := s16c1b_coded_conj (e := e) hgc
  have hcq : s16c1b_conjC e c ∈ s16c1b_Q :=
    List.contains_iff_mem.mp (List.all_eq_true.mp h c hc)
  exact s16c1b_QcodesSub_le_Qsub ⟨s16c1b_conjC e c, hcq, hcode⟩

private theorem s16c1b_map_conj_eq_of_le {S : Subgroup (MulAut (Multiplicative V₀))}
    {a : MulAut (Multiplicative V₀)}
    (h : S.map (MulAut.conj a).toMonoidHom ≤ S)
    (h' : S.map (MulAut.conj a⁻¹).toMonoidHom ≤ S) :
    S.map (MulAut.conj a).toMonoidHom = S := by
  apply le_antisymm h
  have h2 := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) h'
  rw [Subgroup.map_map] at h2
  have hcomp : ((MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom) =
      MonoidHom.id (MulAut (Multiplicative V₀)) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rwa [hcomp, Subgroup.map_id] at h2

private theorem s16c1b_Qsub_mem_normalizer {e : List ℕ}
    (he : s16c1b_Q.all (fun q => s16c1b_Q.contains (s16c1b_conjC e q)) = true)
    (herev : s16c1b_Q.all (fun q => s16c1b_Q.contains (s16c1b_conjC e.reverse q)) = true) :
    s16c1b_κ (wordProd e) ∈
      normalizer ((s16c1b_Qsub.map s16c1b_κ : Subgroup (MulAut (Multiplicative V₀))) :
        Set (MulAut (Multiplicative V₀))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply s16c1b_map_conj_eq_of_le
  · exact s16c1b_Qsub_conj he
  · have h := s16c1b_Qsub_conj herev
    rw [← wordProd_inv e, map_inv] at h
    exact h

private theorem s16c1b_E_le_Omega : s16c1b_E ≤ s16c1b_ΩM := by
  unfold s16c1b_E
  rw [Subgroup.closure_le]
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_map_of_mem _
      (s16c1b_okWord_omega (by decide +kernel : s16c1b_okWord [49,3] = true))
  · exact Subgroup.mem_map_of_mem _
      (s16c1b_okWord_omega (by decide +kernel : s16c1b_okWord [56,48,31,12] = true))

private theorem s16c1b_E_le_normalizer_Q :
    s16c1b_E ≤ normalizer ((s16c1b_Qsub.map s16c1b_κ :
      Subgroup (MulAut (Multiplicative V₀))) : Set (MulAut (Multiplicative V₀))) := by
  unfold s16c1b_E
  rw [Subgroup.closure_le]
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact s16c1b_Qsub_mem_normalizer s16c1b_Q_conj_e1 s16c1b_Q_conj_e1rev
  · exact s16c1b_Qsub_mem_normalizer s16c1b_Q_conj_e2 s16c1b_Q_conj_e2rev

private noncomputable def s16c1b_Ai (i : Fin 3) : Subgroup (MulAut (Multiplicative V₀)) :=
  (s16c1b_Asub i).map s16c1b_κ

theorem s16c1b_join_SM (𝒮 : Set (Subgroup (MulAut (Multiplicative V₀))))
    (h𝒮 : ∀ A ∈ 𝒮, A ∈ E3.aSet 2 s16c1b_ΩM ∧ A ≤ s16c1b_SM)
    (hst : ∀ A ∈ 𝒮, ∀ n ∈ normalizer (s16c1b_SM : Set (MulAut (Multiplicative V₀))) ⊓ s16c1b_ΩM,
      A.map (MulAut.conj n).toMonoidHom ∈ 𝒮) :
    ∃ E : Subgroup (MulAut (Multiplicative V₀)),
      E ≤ normalizer ((⨆ A ∈ 𝒮, A : Subgroup (MulAut (Multiplicative V₀))) :
        Set (MulAut (Multiplicative V₀))) ⊓ s16c1b_ΩM ∧ IsPGroup 3 E ∧ ¬ IsCyclic E := by
  classical
  haveI : Finite (MulAut (Multiplicative V₀)) :=
    Finite.of_injective
      (fun f : MulAut (Multiplicative V₀) => (f : Multiplicative V₀ → Multiplicative V₀))
      (fun f g h => MulEquiv.ext (congrFun h))
  have hp := s16c1b_closure_pair s16c1b_kappa_g1_cube s16c1b_kappa_g2_cube
    s16c1b_kappa_comm s16c1b_kappa_g1_ne_one s16c1b_kappa_g2_ne_one
    s16c1b_kappa_g2_ne_g1 s16c1b_kappa_g2_ne_g1sq
  by_cases hne : 𝒮 = ∅
  · have hjoin : (⨆ A ∈ 𝒮, A : Subgroup (MulAut (Multiplicative V₀))) = ⊥ := by
      rw [hne]; simp
    refine ⟨s16c1b_E, ?_, hp.1, hp.2⟩
    rw [hjoin]
    refine le_inf ?_ s16c1b_E_le_Omega
    intro g _
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simp
  · obtain ⟨A₀, hA₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨j, hj⟩ := s16c1b_classify (h𝒮 A₀ hA₀).1 (h𝒮 A₀ hA₀).2
    have hj' : s16c1b_Ai j ∈ 𝒮 := by
      change (s16c1b_Asub j).map s16c1b_κ ∈ 𝒮
      rw [← hj]; exact hA₀
    have hstep : ∀ i : Fin 3,
        (s16c1b_Ai i).map (MulAut.conj (s16c1b_κ (wordProd [50,3]))).toMonoidHom =
          s16c1b_Ai (i + 1) := by
      intro i
      unfold s16c1b_Ai
      rw [← s16c1b_map_conj_κ (wordProd [50,3]) (s16c1b_Asub i), s16c1b_Asub_conj_n1]
    have hj1 : s16c1b_Ai (j + 1) ∈ 𝒮 := by
      have h := hst (s16c1b_Ai j) hj' (s16c1b_κ (wordProd [50,3])) s16c1b_n1_mem
      rwa [hstep j] at h
    have hj2 : s16c1b_Ai ((j + 1) + 1) ∈ 𝒮 := by
      have h := hst (s16c1b_Ai (j + 1)) hj1 (s16c1b_κ (wordProd [50,3])) s16c1b_n1_mem
      rwa [hstep (j + 1)] at h
    have hrange : Set.range s16c1b_Ai ⊆ 𝒮 := by
      rintro A ⟨i, rfl⟩
      have hi : i = j ∨ i = j + 1 ∨ i = (j + 1) + 1 := by
        fin_cases i <;> fin_cases j <;> simp
      rcases hi with rfl | rfl | rfl
      · exact hj'
      · exact hj1
      · exact hj2
    have hset : 𝒮 = Set.range s16c1b_Ai := by
      ext A
      constructor
      · intro hA
        obtain ⟨i, hi⟩ := s16c1b_classify (h𝒮 A hA).1 (h𝒮 A hA).2
        exact ⟨i, hi.symm⟩
      · intro hA
        exact hrange hA
    have hjoin : (⨆ A ∈ 𝒮, A : Subgroup (MulAut (Multiplicative V₀))) =
        s16c1b_Qsub.map s16c1b_κ := by
      rw [hset, iSup_range]
      change (⨆ i : Fin 3, (s16c1b_Asub i).map s16c1b_κ) = s16c1b_Qsub.map s16c1b_κ
      rw [← Subgroup.map_iSup]
      rfl
    refine ⟨s16c1b_E, ?_, hp.1, hp.2⟩
    rw [hjoin]
    exact le_inf s16c1b_E_le_normalizer_Q s16c1b_E_le_Omega

theorem s16c1b_a2Join_model : OmegaA2Join s16c1b_ΩM := by
  intro S hS 𝒮 h𝒮 hst
  obtain ⟨h, hh, rfl⟩ := s16c1b_sylow_conj hS
  let d : MulAut (Multiplicative V₀) →* MulAut (Multiplicative V₀) :=
    (MulAut.conj h).toMonoidHom
  let d' : MulAut (Multiplicative V₀) →* MulAut (Multiplicative V₀) :=
    (MulAut.conj h⁻¹).toMonoidHom
  have hcomp₁ : d.comp d' = MonoidHom.id _ := by
    ext x; simp [d, d', MulAut.conj_apply, mul_assoc]
  have hcomp₂ : d'.comp d = MonoidHom.id _ := by
    ext x; simp [d, d', MulAut.conj_apply, mul_assoc]
  have hd_inj : Function.Injective d := (MulAut.conj h).injective
  let 𝒮' : Set (Subgroup (MulAut (Multiplicative V₀))) := Subgroup.map d' '' 𝒮
  have hh_inv : h⁻¹ ∈ s16c1b_ΩM := s16c1b_ΩM.inv_mem hh
  have h𝒮' : ∀ A ∈ 𝒮', A ∈ E3.aSet 2 s16c1b_ΩM ∧ A ≤ s16c1b_SM := by
    rintro A ⟨B, hB, rfl⟩
    refine ⟨(s16c1b_aSet_conj hh_inv).2 (h𝒮 B hB).1, ?_⟩
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp ((h𝒮 B hB).2 hb)
    have hthis : d' ((MulAut.conj h).toMonoidHom y) = y := by
      have := congrArg (fun (φ : MulAut (Multiplicative V₀) →*
        MulAut (Multiplicative V₀)) => φ y) hcomp₂
      simpa [MonoidHom.comp_apply, d, d'] using this
    rw [← hyb, hthis]
    exact hy
  have hst' : ∀ A ∈ 𝒮', ∀ n ∈ normalizer (s16c1b_SM : Set (MulAut (Multiplicative V₀))) ⊓
      s16c1b_ΩM, A.map (MulAut.conj n).toMonoidHom ∈ 𝒮' := by
    rintro A ⟨B, hB, rfl⟩ n hn
    obtain ⟨hnN, hnΩ⟩ := Subgroup.mem_inf.mp hn
    let n' : MulAut (Multiplicative V₀) := d n
    have hn'N : n' ∈ normalizer ((s16c1b_SM.map d : Subgroup (MulAut (Multiplicative V₀))) :
        Set (MulAut (Multiplicative V₀))) := by
      have h1 : n' ∈ (normalizer (s16c1b_SM : Set (MulAut (Multiplicative V₀)))).map d := by
        simpa [n'] using Subgroup.mem_map_of_mem d hnN
      rw [Subgroup.map_equiv_normalizer_eq s16c1b_SM (MulAut.conj h)] at h1
      exact h1
    have hn'Ω : n' ∈ s16c1b_ΩM :=
      s16c1b_ΩM.mul_mem (s16c1b_ΩM.mul_mem hh hnΩ) (s16c1b_ΩM.inv_mem hh)
    have hn'mem : n' ∈ normalizer ((s16c1b_SM.map d : Subgroup (MulAut (Multiplicative V₀))) :
        Set (MulAut (Multiplicative V₀))) ⊓ s16c1b_ΩM :=
      Subgroup.mem_inf.mpr ⟨hn'N, hn'Ω⟩
    have hB' : B.map (MulAut.conj n').toMonoidHom ∈ 𝒮 := hst B hB n' hn'mem
    refine ⟨B.map (MulAut.conj n').toMonoidHom, hB', ?_⟩
    have hhom : ((MulAut.conj n).toMonoidHom.comp d') =
        (d'.comp (MulAut.conj n').toMonoidHom) := by
      apply MonoidHom.ext
      intro x
      apply MulEquiv.ext
      intro y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, d, d', n']
      group
    rw [Subgroup.map_map, Subgroup.map_map, hhom]
  have hjoin' : (⨆ A ∈ 𝒮, A).map d' = ⨆ A' ∈ 𝒮', A' := by
    calc (⨆ A ∈ 𝒮, A).map d'
        = ⨆ A ∈ 𝒮, A.map d' := by simp only [Subgroup.map_iSup]
      _ = ⨆ A' ∈ 𝒮', A' :=
            (iSup_image (f := Subgroup.map d') (g := fun A' : Subgroup _ => A')).symm
  have hjoinmap : (⨆ A' ∈ 𝒮', A').map d = ⨆ A ∈ 𝒮, A := by
    rw [← hjoin', Subgroup.map_map, hcomp₁, Subgroup.map_id]
  have hOmega_map : s16c1b_ΩM.map d = s16c1b_ΩM := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact s16c1b_ΩM.mul_mem (s16c1b_ΩM.mul_mem hh hy) (s16c1b_ΩM.inv_mem hh)
    · intro x hx
      refine ⟨MulAut.conj h⁻¹ x, ?_, ?_⟩
      · exact s16c1b_ΩM.mul_mem (s16c1b_ΩM.mul_mem hh_inv hx) (s16c1b_ΩM.inv_mem hh_inv)
      · show (MulAut.conj h) (MulAut.conj h⁻¹ x) = x
        simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨E', hE'le, hE'P, hE'nc⟩ := s16c1b_join_SM 𝒮' h𝒮' hst'
  refine ⟨E'.map d, ?_, hE'P.map d, ?_⟩
  · have h1 := Subgroup.map_mono (f := d) hE'le
    have h2 : (normalizer ((⨆ A ∈ 𝒮', A : Subgroup (MulAut (Multiplicative V₀))) :
        Set (MulAut (Multiplicative V₀))) ⊓ s16c1b_ΩM).map d =
        normalizer ((⨆ A ∈ 𝒮, A : Subgroup (MulAut (Multiplicative V₀))) :
          Set (MulAut (Multiplicative V₀))) ⊓ s16c1b_ΩM := by
      rw [Subgroup.map_inf _ _ d hd_inj,
        Subgroup.map_equiv_normalizer_eq (⨆ A ∈ 𝒮', A) (MulAut.conj h), hjoinmap,
        hOmega_map]
    exact h1.trans (le_of_eq h2)
  · intro hc
    exact hE'nc ((Subgroup.equivMapOfInjective E' d hd_inj).isCyclic.2 hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
