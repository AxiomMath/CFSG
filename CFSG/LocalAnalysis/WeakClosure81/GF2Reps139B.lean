module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_commutator_eq_self_of_isQuasisimple {B : Type*} [Group B]
    {K : Subgroup B} (hq : CFSG.Open.IsQuasisimple K) : ⁅K, K⁆ = K := by
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  exact Subgroup.commutator_eq_self

private theorem w1369_mulAut_comm_of_isCyclic {H : Type*} [Group H] [IsCyclic H] :
    ∀ a b : MulAut H, a * b = b * a := by
  intro a b
  have h := mul_comm ((IsCyclic.mulAutMulEquiv H) a) ((IsCyclic.mulAutMulEquiv H) b)
  refine (IsCyclic.mulAutMulEquiv H).injective ?_
  simpa only [map_mul] using h

private theorem w1369_commSub_invariant_of_normalizes {V : Type*} [CommGroup V]
    {R : Subgroup (MulAut V)} {g : MulAut V} (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∀ u ∈ commSub ⊤ R, g u ∈ commSub ⊤ R := by
  intro u hu
  rw [commSub] at hu ⊢
  refine Subgroup.closure_induction (p := fun c _ =>
    g c ∈ Subgroup.closure {c | ∃ x ∈ R, ∃ w ∈ (⊤ : Subgroup V), x w * w⁻¹ = c})
    ?_ ?_ ?_ ?_ hu
  · rintro c ⟨r, hr, w, -, rfl⟩
    refine Subgroup.subset_closure ⟨g * r * g⁻¹, hg r hr, g w, Subgroup.mem_top _, ?_⟩
    rw [show (g * r * g⁻¹) (g w) = g (r w) from by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]]
    simp
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (Subgroup.closure _).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (Subgroup.closure _).inv_mem ha

private theorem w1369_commSub_invariant_self {V : Type*} [CommGroup V]
    {R : Subgroup (MulAut V)} : StableUnder R (commSub ⊤ R) :=
  fun r hr => w1369_commSub_invariant_of_normalizes
    (fun s hs => R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr))

private theorem w1369_component_le_commutator_swap {K A G : Subgroup (MulAut W)} {d : MulAut W}
    (hK : IsComponentOf K G) (hA : IsComponentOf A G) (hKA : K ≠ A)
    (hdKA : K.map (MulAut.conj d).toMonoidHom = A) :
    K ≤ ⁅K ⊔ A, Subgroup.zpowers d⁆ := by
  have hKAcomm : ∀ a ∈ K, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hA hKA ha hb
  have hperfK : ⁅K, K⁆ = K := w1369_commutator_eq_self_of_isQuasisimple hK.2.2
  have hNnorm : K ⊔ A ≤
      Subgroup.normalizer (⁅K ⊔ A, Subgroup.zpowers d⁆ : Subgroup (MulAut W)) :=
    Subgroup.normalizer_commutator_ge_left (K ⊔ A) (Subgroup.zpowers d)
  have hcomm : ⁅⁅K ⊔ A, Subgroup.zpowers d⁆, K ⊔ A⁆ ≤
      ⁅K ⊔ A, Subgroup.zpowers d⁆ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hNnorm
  have hKK : ⁅K, K⁆ ≤ ⁅K ⊔ A, Subgroup.zpowers d⁆ := by
    rw [Subgroup.commutator_le]
    intro v hv k₁ hk₁
    have hvY : v ∈ K ⊔ A := Subgroup.mem_sup_left hv
    have hk₁Y : k₁ ∈ K ⊔ A := Subgroup.mem_sup_left hk₁
    have hy : ⁅v, d⁆ ∈ ⁅K ⊔ A, Subgroup.zpowers d⁆ :=
      Subgroup.commutator_mem_commutator (H₁ := K ⊔ A) (H₂ := Subgroup.zpowers d)
        hvY (Subgroup.mem_zpowers d)
    have hcA : MulAut.conj d (v⁻¹) ∈ A := by
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj d).toMonoidHom (K.inv_mem hv)
      rwa [hdKA] at hmem
    have hc1 : ⁅MulAut.conj d (v⁻¹), k₁⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hKAcomm k₁ hk₁ (MulAut.conj d (v⁻¹)) hcA).symm
    have hyk₁ : ⁅⁅v, d⁆, k₁⁆ ∈ ⁅K ⊔ A, Subgroup.zpowers d⁆ :=
      hcomm (Subgroup.commutator_mem_commutator
        (H₁ := ⁅K ⊔ A, Subgroup.zpowers d⁆) (H₂ := K ⊔ A) hy hk₁Y)
    have heq : ⁅⁅v, d⁆, k₁⁆ = ⁅v, k₁⁆ := by
      have h := commutatorElement_mul_left_eq_conj_mul v (MulAut.conj d (v⁻¹)) k₁
      have hyv : ⁅v, d⁆ = v * MulAut.conj d (v⁻¹) := by
        simp [commutatorElement_def, MulAut.conj_apply, mul_assoc]
      rw [hyv, h, hc1]
      simp
    rwa [heq] at hyk₁
  simpa only [hperfK] using hKK

theorem Std139.lemmaB (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {R : Subgroup (MulAut W)} {d : MulAut W} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hRX : ∀ r ∈ R, ∀ x ∈ X, r * x = x * r) (hRperf : ⁅R, R⁆ = R) (hR1 : R ≠ ⊥)
    (hdR : R.map (MulAut.conj d).toMonoidHom = R) (hRd : ⁅R, Subgroup.zpowers d⁆ = R) :
    commSub (commSub ⊤ R) (Subgroup.zpowers d) = commSub ⊤ (Subgroup.zpowers d) ∧
      commSub ⊤ (Subgroup.zpowers d) ≤ commSub ⊤ R := by
  let U : Subgroup W := commSub ⊤ R
  have hUX : StableUnder X U :=
    CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := R) (B := X) (M := ⊤) hRX
      (fun _ _ _ _ => Subgroup.mem_top _)
  have hcommY : ∀ y ∈ Subgroup.zpowers d, ∀ b ∈ X, y * b = b * y := by
    intro y hy b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute d b from S.DX d hd b hb) i).eq
  have hUcommX : StableUnder X (commSub U (Subgroup.zpowers d)) :=
    CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := Subgroup.zpowers d) (B := X)
      (M := U) hcommY hUX
  have hne : commSub U (Subgroup.zpowers d) ≠ ⊥ := by
    intro hbot
    have hUfix : U ≤ fixV (Subgroup.zpowers d) := commSub_eq_bot_iff.mp hbot
    have hdUfix : ∀ (j : ℤ), ∀ u ∈ U, (d ^ j) u = u :=
      fun j u hu => (mem_fixV.mp (hUfix hu)) (d ^ j) (Subgroup.zpow_mem_zpowers d j)
    have hUR : StableUnder R U := w1369_commSub_invariant_self
    have hcomm_le : ⁅R, Subgroup.zpowers d⁆ ≤ centSub U := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [mem_centSub]
      intro u hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have h1 : a⁻¹ u ∈ U := hUR a⁻¹ (R.inv_mem ha) u hu
      calc (⁅a, d ^ j⁆) u
          = a ((d ^ j) (a⁻¹ ((d ^ j)⁻¹ u))) := by
              simp [commutatorElement_def, MulAut.mul_apply]
        _ = a ((d ^ j) (a⁻¹ u)) := by
              rw [show (d ^ j)⁻¹ = d ^ (-j) from by rw [← zpow_neg]]
              rw [hdUfix (-j) u hu]
        _ = a (a⁻¹ u) := by rw [hdUfix j (a⁻¹ u) h1]
        _ = u := by simp
    have hRle : R ≤ centSub U := hRd ▸ hcomm_le
    have hUtriv : commSub U R = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro u hu r hr
      exact (mem_centSub.mp (hRle hr)) u hu
    have hchain : commSub ⊤ R ≤ ⊥ :=
      CFSG.LocalAnalysis.WeakClosure81.s13_perfect_chain R hRperf ⊥ U ⊤
        (le_of_eq hUtriv) le_rfl
    have hUbot : commSub ⊤ R = ⊥ := le_bot_iff.mp hchain
    have hfixR : fixV R = ⊤ := top_le_iff.mp (commSub_eq_bot_iff.mp hUbot)
    have hRbot : R = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro r hr
      ext w
      have hw : w ∈ fixV R := by rw [hfixR]; exact Subgroup.mem_top w
      exact mem_fixV.mp hw r hr
    exact hR1 hRbot
  have hle : commSub U (Subgroup.zpowers d) ≤ commSub ⊤ (Subgroup.zpowers d) :=
    commSub_mono le_top le_rfl
  obtain ⟨x, hxgen, hx3, hxne, hfixX, hsx⟩ := Std139.exists_gen hw2 S
  have hrkU : 2 ≤ rk ↥(commSub U (Subgroup.zpowers d)) :=
    xstable_two_le_rk hw2 hfixX hUcommX hne
  have hrkW : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 2 :=
    (Std139.commSub_axis hw2 S hd hd1).1
  have heq : commSub U (Subgroup.zpowers d) = commSub ⊤ (Subgroup.zpowers d) :=
    eq_of_le_of_rk_le hw2 hle (by rw [hrkW]; exact hrkU)
  have hdR' : ∀ r ∈ R, d * r * d⁻¹ ∈ R := by
    intro r hr
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj d).toMonoidHom hr
    rw [hdR] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hdU : ∀ u ∈ U, d u ∈ U := w1369_commSub_invariant_of_normalizes hdR'
  have hdstab : d ∈ stabSub U := by
    have hdUmap : U.map d.toMonoidHom ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact hdU u hu
    have hdUeq : U.map d.toMonoidHom = U := by
      refine Subgroup.eq_of_le_of_card_ge hdUmap ?_
      rw [Subgroup.card_map_of_injective d.injective]
    rw [mem_stabSub]
    intro u
    constructor
    · intro hdu
      have hdu' : d u ∈ U.map d.toMonoidHom := by rw [hdUeq]; exact hdu
      obtain ⟨s, hs, hsd⟩ := Subgroup.mem_map.mp hdu'
      exact (d.injective hsd) ▸ hs
    · exact hdU u
  have hzp : Subgroup.zpowers d ≤ stabSub U := Subgroup.zpowers_le.mpr hdstab
  have hleU : commSub U (Subgroup.zpowers d) ≤ U :=
    commSub_le_of_invariant (fun y hy u hu => (mem_stabSub.mp (hzp hy) u).2 hu)
  exact ⟨heq, heq ▸ hleU⟩

theorem comm_eq_self_of_component {K : Subgroup (MulAut W)} (hK : IsComponentOf K G)
    {d : MulAut W} (hdK : K.map (MulAut.conj d).toMonoidHom = K)
    (hne : ⁅K, Subgroup.zpowers d⁆ ≠ ⊥) : ⁅K, Subgroup.zpowers d⁆ = K := by
  have hdmem : d ∈ Subgroup.normalizer (K : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hdK
  have hzd : Subgroup.zpowers d ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr hdmem
  have hNKle : ⁅K, Subgroup.zpowers d⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hzd
  haveI : ((⁅K, Subgroup.zpowers d⁆).subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.normalizer_commutator_ge_left K (Subgroup.zpowers d))
  have hperf : ⁅K, K⁆ = K := w1369_commutator_eq_self_of_isQuasisimple hK.2.2
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK.2.2
    ((⁅K, Subgroup.zpowers d⁆).subgroupOf K) with hcenter | htop
  · exfalso
    have hmem_comm : ∀ n ∈ ⁅K, Subgroup.zpowers d⁆, ∀ k ∈ K, n * k = k * n := by
      intro n hn k hk
      have hnK : n ∈ K := hNKle hn
      have hcen : (⟨n, hnK⟩ : ↥K) ∈ (⁅K, Subgroup.zpowers d⁆).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hn
      have hc := Subgroup.mem_center_iff.mp (hcenter hcen) (⟨k, hk⟩ : ↥K)
      exact (congrArg Subtype.val hc).symm
    have hNKbot : ⁅⁅K, Subgroup.zpowers d⁆, K⁆ = ⊥ :=
      le_bot_iff.mp (Subgroup.commutator_le.mpr
        (fun n hn k hk => commutatorElement_eq_one_iff_mul_comm.mpr (hmem_comm n hn k hk)))
    have h2 : ⁅⁅Subgroup.zpowers d, K⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (Subgroup.zpowers d) K]
      exact hNKbot
    have h3 : ⁅⁅K, K⁆, Subgroup.zpowers d⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K)
        (H₃ := Subgroup.zpowers d) hNKbot h2
    rw [hperf] at h3
    exact hne h3
  · have hKNle : K ≤ ⁅K, Subgroup.zpowers d⁆ := Subgroup.subgroupOf_eq_top.mp htop
    exact le_antisymm hNKle hKNle

theorem swap_comm_eq_self {K : Subgroup (MulAut W)} (hK : IsComponentOf K G) {d : MulAut W}
    (hd : d ∈ G) (hd2 : d ^ 2 = 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) :
    ⁅swapPair K d, Subgroup.zpowers d⁆ = swapPair K d ∧
      ⁅swapPair K d, swapPair K d⁆ = swapPair K d := by
  let K' : Subgroup (MulAut W) := K.map (MulAut.conj d).toMonoidHom
  let Y : Subgroup (MulAut W) := K ⊔ K'
  have hK' : IsComponentOf K' G := CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK hd
  have hneKK' : K ≠ K' := Ne.symm hKd
  have hperfK : ⁅K, K⁆ = K := w1369_commutator_eq_self_of_isQuasisimple hK.2.2
  have hperfK' : ⁅K', K'⁆ = K' := w1369_commutator_eq_self_of_isQuasisimple hK'.2.2
  have hconj_sq : (MulAut.conj d : MulAut (MulAut W)) * MulAut.conj d = 1 := by
    rw [← map_mul, ← pow_two, hd2, map_one]
  have hconj_dd : ∀ x : MulAut W, MulAut.conj d (MulAut.conj d x) = x := by
    intro x
    have h := congrArg (fun (f : MulAut (MulAut W)) => f x) hconj_sq
    simpa [MulAut.mul_apply] using h
  have hK'map : K'.map (MulAut.conj d).toMonoidHom = K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
      show (MulAut.conj d) ((MulAut.conj d) k) ∈ K
      rw [hconj_dd k]
      exact hk
    · intro hy
      exact ⟨MulAut.conj d y, Subgroup.mem_map_of_mem _ hy, hconj_dd y⟩
  have hdY : Y.map (MulAut.conj d).toMonoidHom = Y := by
    show (K ⊔ K').map (MulAut.conj d).toMonoidHom = K ⊔ K'
    rw [Subgroup.map_sup, hK'map]
    exact sup_comm K' K
  have hdmemY : d ∈ Subgroup.normalizer (Y : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hdY
  have hzpY : Subgroup.zpowers d ≤ Subgroup.normalizer (Y : Set (MulAut W)) :=
    Subgroup.zpowers_le.mpr hdmemY
  have hNY : ⁅Y, Subgroup.zpowers d⁆ ≤ Y :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hzpY
  have hKleN : K ≤ ⁅Y, Subgroup.zpowers d⁆ :=
    w1369_component_le_commutator_swap hK hK' hneKK' (rfl : K.map _ = K')
  have hK'leN' : K' ≤ ⁅K' ⊔ K, Subgroup.zpowers d⁆ :=
    w1369_component_le_commutator_swap hK' hK hKd hK'map
  have hK'leN : K' ≤ ⁅Y, Subgroup.zpowers d⁆ := by
    show K' ≤ ⁅K ⊔ K', Subgroup.zpowers d⁆
    simpa only [sup_comm K' K] using hK'leN'
  have hYleN : Y ≤ ⁅Y, Subgroup.zpowers d⁆ := sup_le hKleN hK'leN
  have hN : ⁅Y, Subgroup.zpowers d⁆ = Y := le_antisymm hNY hYleN
  have hYperf : ⁅Y, Y⁆ = Y := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
    · have h1 : K ≤ ⁅Y, Y⁆ := by
        simpa only [hperfK] using
          Subgroup.commutator_mono (le_sup_left : K ≤ Y) (le_sup_left : K ≤ Y)
      have h2 : K' ≤ ⁅Y, Y⁆ := by
        simpa only [hperfK'] using
          Subgroup.commutator_mono (le_sup_right : K' ≤ Y) (le_sup_right : K' ≤ Y)
      exact sup_le h1 h2
  exact ⟨hN, hYperf⟩

theorem Std139.component_commutes_X (S : Std139 G X D s Y n) {K : Subgroup (MulAut W)}
    (hK : IsComponentOf K G) : ∀ k ∈ K, ∀ x ∈ X, k * x = x * k := by
  have hcard3 : Nat.card ↥(X.subgroupOf G) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.XG).toEquiv]
    exact S.Xcard
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsCyclic ↥(X.subgroupOf G) := isCyclic_of_prime_card (p := 3) hcard3
  haveI : IsMulCommutative (MulAut ↥(X.subgroupOf G)) :=
    IsMulCommutative.of_comm (w1369_mulAut_comm_of_isCyclic)
  have hXGn : (X.subgroupOf G).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact S.Xnorm (g : MulAut W) g.2 (x : MulAut W) hx⟩
  letI : (X.subgroupOf G).Normal := hXGn
  let φ : ↥K →* MulAut ↥(X.subgroupOf G) :=
    (MulAut.conjNormal (H := X.subgroupOf G)).comp (Subgroup.inclusion hK.1)
  have hφker : φ.ker = ⊤ := by
    have h := Abelianization.commutator_subset_ker φ
    rw [hK.2.2.1] at h
    exact top_le_iff.mp h
  intro k hk x hx
  have hφk : φ ⟨k, hk⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hφker]
    exact Subgroup.mem_top _
  let z : ↥(X.subgroupOf G) := ⟨⟨x, S.XG hx⟩, hx⟩
  have hval : ((MulAut.conjNormal (Subgroup.inclusion hK.1 ⟨k, hk⟩)) z : ↥G) = (z : ↥G) := by
    simpa [φ, z] using congrArg (fun ψ : MulAut ↥(X.subgroupOf G) => (ψ z : ↥G)) hφk
  have hkx : (k : MulAut W) * x * (k : MulAut W)⁻¹ = x := by
    have h := congrArg Subtype.val hval
    rw [MulAut.conjNormal_apply] at h
    simpa [Subgroup.coe_inclusion, z] using h
  calc (k : MulAut W) * x = ((k : MulAut W) * x * (k : MulAut W)⁻¹) * (k : MulAut W) := by
        group
    _ = x * (k : MulAut W) := by rw [hkx]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
