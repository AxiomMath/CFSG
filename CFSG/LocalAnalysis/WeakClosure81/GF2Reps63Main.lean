module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63Fix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63Setup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63Quot
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63Core
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

private lemma commV_zpowers_map_fix {Q : Type*} [Group Q] {V : Type*} [CommGroup V]
    {N : Subgroup Q} {W : Subgroup V} (σ : ↥N →* MulAut (V ⧸ W)) (ρ : Q →* MulAut V)
    (hσ : ∀ (n : ↥N) (v : V), σ n (QuotientGroup.mk v) = QuotientGroup.mk (ρ n v))
    {a : Q} {a' : ↥N} (haQ : (a' : Q) = a) (ha' : a' * a' = 1) {y' : ↥N}
    (hy : ∀ v : V, ρ (y' : Q) (ρ a v * v⁻¹) = ρ a v * v⁻¹) :
    ∀ w ∈ commV (Subgroup.zpowers (σ a')), σ y' w = w := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, u, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    have h2 : (σ a') ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← map_mul, ha', map_one]
    rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [hk]
      simp
    · rw [hk]
      have h1 : σ a' (QuotientGroup.mk v) = QuotientGroup.mk (ρ a v) := by
        rw [hσ a' v, haQ]
      have hfix : σ y' (QuotientGroup.mk (ρ a v * v⁻¹)) =
          QuotientGroup.mk (ρ a v * v⁻¹) := by
        rw [hσ y' (ρ a v * v⁻¹), hy v]
      calc
        σ y' (((σ a') ^ (1 : ℤ)) (QuotientGroup.mk v) * (QuotientGroup.mk v)⁻¹)
            = σ y' (QuotientGroup.mk (ρ a v) * (QuotientGroup.mk v)⁻¹) := by
              rw [zpow_one, h1]
        _ = σ y' (QuotientGroup.mk (ρ a v * v⁻¹)) := by
              rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        _ = QuotientGroup.mk (ρ a v * v⁻¹) := hfix
        _ = ((σ a') ^ (1 : ℤ)) (QuotientGroup.mk v) * (QuotientGroup.mk v)⁻¹ := by
              rw [zpow_one, h1, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  | one => exact map_one (σ y')
  | mul x y _ _ ihx ihy => rw [map_mul, ihx, ihy]
  | inv x _ ih => rw [map_inv, ih]

private lemma fixV_sup_map_conj_eq_bot {N : Type*} [Group N] {U : Type*} [CommGroup U]
    (σ : N →* MulAut U) {X Y : Subgroup N} {g : N} {S : Set N}
    (hXS : X ≤ Subgroup.closure S)
    (hS : ∀ s ∈ S, s ∈ Y ∨ s ∈ Y.map (MulAut.conj g).toMonoidHom)
    (hfix : ∀ u : U, (∀ x ∈ X, σ x u = u) → u = 1) :
    fixV (Y.map σ ⊔ (Y.map σ).map (MulAut.conj (σ g)).toMonoidHom) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  refine hfix u ?_
  intro x hx
  have hfixcl : ∀ z ∈ Subgroup.closure S, σ z u = u := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem s hs =>
      rcases hS s hs with hsY | hsYmap
      · exact (mem_fixV.mp hu) (σ s) (Subgroup.mem_sup_left
          (Subgroup.mem_map.mpr ⟨s, hsY, rfl⟩))
      · obtain ⟨y, hyY, hys⟩ := Subgroup.mem_map.mp hsYmap
        have heq : σ s = (MulAut.conj (σ g)) (σ y) := by
          rw [← hys]
          simp [MulAut.conj_apply]
        rw [heq]
        exact (mem_fixV.mp hu) _ (Subgroup.mem_sup_right
          (Subgroup.mem_map.mpr ⟨σ y, Subgroup.mem_map.mpr ⟨y, hyY, rfl⟩, rfl⟩))
    | one => simp
    | mul x y _ _ ihx ihy => rw [map_mul, MulAut.mul_apply, ihy, ihx]
    | inv x _ ih =>
      rw [map_inv]
      apply (σ x).injective
      simpa using ih.symm
  exact hfixcl x (hXS hx)

theorem asch6_3Even_holds :
    ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ ρ : Q →* MulAut V, Function.Injective ρ →
      ∀ (a : Q) (L A : Subgroup Q), orderOf a = 2 → IsComponentOf L ⊤ → Nat.card A = 4 →
        IsElemAbelian 2 A → a ∈ A → (∀ b ∈ A, ∀ v : V, ρ b (ρ a v * v⁻¹) = ρ a v * v⁻¹) →
        A ⊓ centralizer (L : Set Q) = ⊥ →
        (∃ x : ↥L ⧸ center ↥L, Even (orderOf x) ∧ orderOf x ≠ 2) →
        a ∈ normalizer (L : Set Q) := by
  intro Q _ _ V _ _ hV ρ hρ a L A ha hL hA hA2 haA hAV hAL hx
  by_contra haL
  obtain ⟨hLa, b, hbA, hbb, hab, horb⟩ :=
    Asch6.exists_orbit_data ha hL hA hA2 haA hAL haL
  have ha2 : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha, pow_two] at h
  have hperfL : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator, hL.2.2.1, Subgroup.map_top,
      Subgroup.range_subtype]
  have hb : ∀ v : V, ρ b (ρ a v * v⁻¹) = ρ a v * v⁻¹ := hAV b hbA
  have hψ : ∀ y ∈ L, ∀ v : V, ρ (y * (a * y * a)) (ρ a v * v⁻¹) = ρ a v * v⁻¹ := by
    rcases horb with ⟨hbN, hLb⟩ | ⟨hLb, hLab⟩
    · exact Asch6.fixes_commV_diag_of_mem_normalizer ρ ha2 hab hLa hbN hLb hb
    · exact Asch6.fixes_commV_diag_of_commute ρ ha2 hbb hab hLa hLb hLab hperfL hb
  let X : Subgroup Q := Asch6.conjSup L a b
  let N : Subgroup Q := Subgroup.normalizer (X : Set Q)
  have hLX : L ≤ X := Asch6.le_conjSup L a b
  have hXperf : ⁅X, X⁆ = X := Asch6.commutator_conjSup hperfL a b
  have hXleN : X ≤ N := Subgroup.le_normalizer
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have haN : a ∈ N := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => (Asch6.conj_mem_conjSup ha2 hbb hab hy).1
    · intro hy
      have h := (Asch6.conj_mem_conjSup ha2 hbb hab hy).1
      rw [ha_inv] at h
      have hy' : a * (a * y * a) * a = y := by
        calc a * (a * y * a) * a = (a * a) * y * (a * a) := by group
          _ = y := by rw [ha2, one_mul, mul_one]
      rwa [hy'] at h
  have hbN : b ∈ N := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => (Asch6.conj_mem_conjSup ha2 hbb hab hy).2
    · intro hy
      have h := (Asch6.conj_mem_conjSup ha2 hbb hab hy).2
      rw [hb_inv] at h
      have hy' : b * (b * y * b) * b = y := by
        calc b * (b * y * b) * b = (b * b) * y * (b * b) := by group
          _ = y := by rw [hbb, one_mul, mul_one]
      rwa [hy'] at h
  obtain ⟨x, hxeven, hxne2⟩ := hx
  have hLne : L ≠ ⊥ := by
    intro hbot
    haveI : Subsingleton ↥L := by rw [hbot]; infer_instance
    haveI : Subsingleton (↥L ⧸ center ↥L) := inferInstance
    have hx1 : x = 1 := Subsingleton.elim x 1
    have hord : orderOf x = 1 := by rw [hx1]; exact orderOf_one
    rw [hord] at hxeven
    exact Nat.not_even_one hxeven
  have hXmap : X.map ρ ≠ ⊥ := by
    intro hbot
    have hXleker : X ≤ ρ.ker := (Subgroup.map_eq_bot_iff X).mp hbot
    have hkerbot : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff (f := ρ)).mpr hρ
    have hXbot : X = ⊥ := le_bot_iff.mp (hkerbot ▸ hXleker)
    exact hLne (le_bot_iff.mp (hXbot ▸ hLX))
  obtain ⟨W, σ, hσ, ⟨xq, hxqX, hxqσ⟩, hfix⟩ :=
    Asch6.exists_quot_of_perfect (N := N) (X := X) ρ hXleN
      (fun n hn y hy => (Subgroup.mem_normalizer_iff.mp hn y).mp hy) hXperf hXmap
  let aN : ↥N := ⟨a, haN⟩
  have haNQ : (aN : Q) = a := rfl
  have haN2 : aN * aN = 1 := by
    apply Subtype.ext
    simpa [aN] using ha2
  obtain ⟨w, hwL, hwm⟩ := Asch6.exists_pow_commute_iff_dvd (L := L) x
  have hwN : w ∈ N := hLX.trans hXleN hwL
  let wN : ↥N := ⟨w, hwN⟩
  have hU : ∀ u : V ⧸ W, u ^ 2 = 1 := by
    intro u
    induction u using QuotientGroup.induction_on with
    | H v =>
      rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]
  have hLa' : ∀ y ∈ L.subgroupOf N, ∀ z ∈ L.subgroupOf N,
      y * (aN * z * aN) = (aN * z * aN) * y := by
    intro y hy z hz
    apply Subtype.ext
    simpa [aN] using hLa (y : Q) hy (z : Q) hz
  have hwm' : ∀ k : ℕ, (∀ z ∈ L.subgroupOf N, wN ^ k * z = z * wN ^ k) ↔
      orderOf x ∣ k := by
    intro k
    constructor
    · intro h
      refine (hwm k).mp ?_
      intro z hz
      have hzN : (⟨z, hLX.trans hXleN hz⟩ : ↥N) ∈ L.subgroupOf N := hz
      have h' := h _ hzN
      simpa [wN] using congrArg (Subtype.val) h'
    · intro h z hz
      have h' := (hwm k).mpr h (z : Q) hz
      apply Subtype.ext
      simpa [wN] using h'
  have hker : ∀ y ∈ L.subgroupOf N, σ (aN * y⁻¹ * aN * y) = 1 →
      ∀ z ∈ L.subgroupOf N, y * z = z * y := by
    let K : Subgroup Q := (MonoidHom.ker σ).map N.subtype
    have hNK : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
      intro n hn k hk
      obtain ⟨m, hmker, hm⟩ := Subgroup.mem_map.mp hk
      refine Subgroup.mem_map.mpr ⟨(⟨n, hn⟩ : ↥N) * m * (⟨n, hn⟩ : ↥N)⁻¹, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hmker]
        simp
      · simpa using hm
    have hLK : ∀ z ∈ L, ∀ k ∈ K, z * k * z⁻¹ ∈ K := by
      intro z hz k hk
      exact hNK z (hLX.trans hXleN hz) k hk
    have hKnot : ¬ L ≤ K := by
      intro hLKle
      have hXK : X ≤ K := by
        change Asch6.conjSup L a b ≤ K
        rw [Asch6.conjSup]
        refine sup_le (sup_le (sup_le hLKle ?_) ?_) ?_
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          simpa [MulAut.conj_apply] using hNK a haN y (hLKle hy)
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          simpa [MulAut.conj_apply] using hNK b hbN y (hLKle hy)
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          have heq : a * b * y * (b⁻¹ * a⁻¹) = a * (b * y * b⁻¹) * a⁻¹ := by group
          simpa [MulAut.conj_apply, heq] using hNK (a * b) (N.mul_mem haN hbN) y (hLKle hy)
      have hxqK : (xq : Q) ∈ K := hXK hxqX
      obtain ⟨m, hmker, hm⟩ := Subgroup.mem_map.mp hxqK
      have hxq_eq : xq = m := Subtype.ext hm.symm
      exact hxqσ (by rw [hxq_eq]; exact MonoidHom.mem_ker.mp hmker)
    intro y hy hy1 z hz
    have hyQ : (y : Q) ∈ L := hy
    have hyK : a * (y : Q)⁻¹ * a * (y : Q) ∈ K := by
      refine Subgroup.mem_map.mpr ⟨aN * y⁻¹ * aN * y, MonoidHom.mem_ker.mpr hy1, ?_⟩
      simp [aN]
    have hcomm := Asch6.commute_of_mul_mem (L := L) (K := K) hL.2.2 hLK hKnot ha2 hLa hyQ hyK
    apply Subtype.ext
    exact hcomm (z : Q) hz
  have hdisj : ∀ g' ∈ L.subgroupOf N,
      (¬ ∀ y ∈ L.subgroupOf N, g' * y = y * g') →
      commV (zpowers (σ aN)) ⊓ commV (zpowers (σ (g' * aN * g'⁻¹))) = ⊥ := by
    intro g' hg'L hg'nc
    have hgQ : (g' : Q) ∈ L := hg'L
    have hgN : (g' : Q) ∈ N := hLX.trans hXleN hgQ
    have hgcent : (g' : Q) ∉ centralizer (L : Set Q) := by
      intro hc
      apply hg'nc
      intro y hy
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hc (y : Q) hy).symm
    have hgNorm : (g' : Q) ∈ normalizer (L : Set Q) := Subgroup.le_normalizer hgQ
    have hLg := Asch6.le_closure_commutator_of_mem_normalizer hL.2.2 hgNorm hgcent
    let Y₀ : Subgroup Q :=
      Subgroup.closure ((fun y => y * (a * y * a)) '' (L : Set Q) ∪ {b})
    let S : Set Q := (fun y => y * (a * y * a)) '' (L : Set Q) ∪ {b} ∪
      (fun y => (g' : Q) * (y * (a * y * a)) * (g' : Q)⁻¹) '' (L : Set Q)
    have hXclosed : X ≤ Subgroup.closure S :=
      Asch6.conjSup_le_closure ha2 hab hLa hgQ hLg
    let F : Subgroup Q :=
      { carrier := {y | ∀ v : V, ρ y (ρ a v * v⁻¹) = ρ a v * v⁻¹}
        one_mem' := by intro v; simp
        mul_mem' := by
          intro y z hy hz v
          rw [map_mul ρ y z, MulAut.mul_apply, hz v, hy v]
        inv_mem' := by
          intro y hy v
          rw [map_inv]
          apply (ρ y).injective
          simpa using (hy v).symm }
    have hY0F : Y₀ ≤ F := by
      refine (Subgroup.closure_le F).mpr ?_
      rintro y (⟨y₀, hy₀, rfl⟩ | hy)
      · exact hψ y₀ hy₀
      · have hyb : y = b := by simpa using hy
        subst hyb
        exact hb
    have hY : ∀ y ∈ (Y₀.subgroupOf N).map σ,
        ∀ u ∈ commV (zpowers (σ aN)), y u = u := by
      intro y hy u hu
      obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
      exact commV_zpowers_map_fix (a := a) (a' := aN) (y' := y₀) σ ρ hσ haNQ haN2
        (hY0F hy₀) u hu
    let SN : Set ↥N := {z | (z : Q) ∈ S}
    have hS_N : S ⊆ N := by
      intro s hs
      rcases hs with (hs | hs) | hs
      · obtain ⟨y, hyL, rfl⟩ := hs
        have hyX : y ∈ X := hLX hyL
        have hayX : a * y * a ∈ X := by
          have h := (Subgroup.mem_normalizer_iff.mp haN y).mp hyX
          rwa [ha_inv] at h
        exact hXleN (X.mul_mem hyX hayX)
      · have hsb : s = b := by simpa using hs
        subst hsb
        exact hbN
      · obtain ⟨y, hyL, rfl⟩ := hs
        have hyX : y ∈ X := hLX hyL
        have hayX : a * y * a ∈ X := by
          have h := (Subgroup.mem_normalizer_iff.mp haN y).mp hyX
          rwa [ha_inv] at h
        have hψN : y * (a * y * a) ∈ N := hXleN (X.mul_mem hyX hayX)
        exact N.mul_mem (N.mul_mem hgN hψN) (N.inv_mem hgN)
    have hmap_closure : (Subgroup.closure SN).map N.subtype = Subgroup.closure S := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hS_N hz⟩, hz, rfl⟩
    have hXsub_le : X.subgroupOf N ≤ Subgroup.closure SN := by
      intro x hx
      have hxX : (x : Q) ∈ X := hx
      have hxCl : (x : Q) ∈ Subgroup.closure S := hXclosed hxX
      have hxmap : (x : Q) ∈ (Subgroup.closure SN).map N.subtype := by
        rwa [hmap_closure]
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxmap
      have hzx' : z = x := Subtype.ext hzx
      rwa [← hzx']
    have hSgen : ∀ s ∈ SN, s ∈ Y₀.subgroupOf N ∨
        s ∈ (Y₀.subgroupOf N).map (MulAut.conj g').toMonoidHom := by
      intro s hs
      rcases hs with (hs | hs) | hs
      · obtain ⟨y, hyL, hψs⟩ := hs
        left
        exact Subgroup.mem_subgroupOf.mpr (by
          rw [← hψs]
          exact Subgroup.subset_closure (Or.inl ⟨y, hyL, rfl⟩))
      · left
        have hsb : (s : Q) = b := by simpa using hs
        exact Subgroup.mem_subgroupOf.mpr (by
          rw [hsb]
          exact Subgroup.subset_closure (Or.inr rfl))
      · obtain ⟨y, hyL, hψs⟩ := hs
        right
        have hyX : y ∈ X := hLX hyL
        have hayX : a * y * a ∈ X := by
          have h := (Subgroup.mem_normalizer_iff.mp haN y).mp hyX
          rwa [ha_inv] at h
        have hψN : y * (a * y * a) ∈ N := hXleN (X.mul_mem hyX hayX)
        refine Subgroup.mem_map.mpr ⟨⟨y * (a * y * a), hψN⟩, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr
            (Subgroup.subset_closure (Or.inl ⟨y, hyL, rfl⟩))
        · apply Subtype.ext
          simpa [MulAut.conj_apply] using hψs
    have hgen : fixV ((Y₀.subgroupOf N).map σ ⊔
        ((Y₀.subgroupOf N).map σ).map (MulAut.conj (σ g')).toMonoidHom) = ⊥ :=
      fixV_sup_map_conj_eq_bot (X := X.subgroupOf N) (Y := Y₀.subgroupOf N)
        (g := g') (S := SN) σ hXsub_le hSgen (fun u hu => hfix u hu)
    have hres := Asch6.commV_inf_commV_conj_eq_bot (Y := (Y₀.subgroupOf N).map σ)
      (a := σ aN) (h := σ g') hY hgen
    simpa [map_mul, map_inv] using hres
  have hwNmem : wN ∈ L.subgroupOf N := hwL
  exact Asch6.false_of_commV_inf_eq_bot (G := ↥N) (U := V ⧸ W) hU σ haN2 hLa'
    hdisj hker hwNmem hxeven hxne2 hwm'

end CFSG.LocalAnalysis.WeakClosure81

end
