module

public import CFSG.Quasithin.Background.B51SumOffenders
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.InternalSecB56M
public import CFSG.Quasithin.Background.InternalSecBasic

public section

namespace CFSG.Quasithin.FFJImage

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open scoped commutatorElement

variable {V : Type} [CommGroup V]

theorem b53Hyp_ffJ_range {Y : Type} [Group Y] [Finite Y] (hS : SQTKGroup Y) (φ : Y →* MulAut V)
    (hO2 : pCoreOf 2 φ.range = ⊥) : B53Hyp (ffJ φ.range) := by
  set X := φ.range with hX
  set J := ffJ X with hJ
  have hJX : J ≤ X := B6.ffJ_le X
  have hJn : (J.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ X)
  have hQ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J X hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  set H : Subgroup Y := J.comap φ with hH
  let f : ↥H →* ↥J :=
    { toFun := fun h => ⟨φ h, h.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨y, hy⟩ := hJX hj
    refine ⟨⟨y, show φ y ∈ J by rw [hy]; exact hj⟩, ?_⟩
    apply Subtype.ext
    exact hy
  exact ⟨hQ, (ffJ_ffJ _).symm, ↥H, inferInstance, inferInstance, f.ker, inferInstance,
    sqtkGroup_subgroup hS H, ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

theorem b56Cases_two [Finite V] {J K K' : Subgroup (MulAut V)} (hKJ : K ≤ J) (hK'J : K' ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hn' : ∀ x ∈ J, ∀ k ∈ K', x * k * x⁻¹ ∈ K')
    (hK : CFSG.IsQuasisimple ↥K) (hK' : CFSG.IsQuasisimple ↥K')
    (hcomm : commV K ⊔ commV K' = ⊤)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    (quasithinGenFitting J = K ∧ K' = K) ∨ commV K ⊓ commV K' ≤ fixV J := by
  have htop : ∀ {X : Subgroup (MulAut V)}, K ≤ X → K' ≤ X → commV X = ⊤ := fun h h' =>
    top_le_iff.1 (by rw [← hcomm]; exact sup_le (commV_le_commV h) (commV_le_commV h'))
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, -, W₁, W₂, -, -, -, -, -, hWinf, hp₁, hp₂⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, -, hc₂, -, -, ⟨-, hV12⟩, -, hcV₂, ht₁, ht₂, -⟩ |
      ⟨_, _, -, -, -, -, -, -, hidx, -⟩
  · left
    have e1 := eq_of_le_quasisimple hKJ hn hK h1.1
    have e2 := eq_of_le_quasisimple hK'J hn' hK' h1.1
    exact ⟨e1, e2.symm.trans e1⟩
  · exact (not_le_perm_three hK hKJ e).elim
  · rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h <;>
      rcases le_or_le_of_sup_eq hsup hc hK'J hn' hK' with h' | h'
    · exfalso
      have hW₁ : W₁ = ⊤ := top_le_iff.1 ((htop h h').symm.le.trans (commV_le_of_b56Piece hp₁))
      rw [hW₁, top_inf_eq] at hWinf
      rw [hWinf] at hp₂
      exact not_b56Piece_self hp₂
    · right
      rw [← hWinf]
      exact inf_le_inf ((commV_le_commV h).trans (commV_le_of_b56Piece hp₁))
        ((commV_le_commV h').trans (commV_le_of_b56Piece hp₂))
    · right
      rw [← hWinf, inf_comm W₁]
      exact inf_le_inf ((commV_le_commV h).trans (commV_le_of_b56Piece hp₂))
        ((commV_le_commV h').trans (commV_le_of_b56Piece hp₁))
    · exfalso
      have hW₂ : W₂ = ⊤ := top_le_iff.1 ((htop h h').symm.le.trans (commV_le_of_b56Piece hp₂))
      rw [hW₂, inf_top_eq] at hWinf
      rw [hWinf] at hp₁
      exact not_b56Piece_self hp₁
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hK'J hn' hK' with h' | h'
      · rw [htop h h', top_inf_eq] at hV12
        rw [hV12, Subgroup.card_bot] at hcV₂
        norm_num at hcV₂
      · exact not_le_of_card_prime hK' h' hc₂
    · exact not_le_of_card_prime hK h hc₂
  · exfalso
    rw [htop hKJ hK'J, top_sup_eq, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

section Comm

variable {Ω : Type} [Group Ω]

theorem commutator_eq_of_not_le_centralizer {K B : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K)
    (hBK : B ≤ Subgroup.normalizer (K : Set Ω)) (hne : ¬ B ≤ Subgroup.centralizer (K : Set Ω)) :
    ⁅K, B⁆ = K := by
  have hle : ⁅K, B⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hBK
  have hnorm : ((⁅K, B⁆ : Subgroup Ω).subgroupOf K).Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_left K B k.2) _).mp hx
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      (B1Red.isQuasisimple_to_open hK) ((⁅K, B⁆ : Subgroup Ω).subgroupOf K) with hc | htop
  · exfalso
    apply hne
    have hZ : ⁅⁅K, B⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := Subgroup.mem_center_iff.mp (hc (show (⟨x, hle hx⟩ : ↥K) ∈
        (⁅K, B⁆ : Subgroup Ω).subgroupOf K from hx)) ⟨k, hk⟩
      exact congrArg Subtype.val h1
    have hZ' : ⁅⁅B, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm B K]; exact hZ
    have h3 : ⁅⁅K, K⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hZ hZ'
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
    rw [hperf, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (h3 hk) b hb).symm
  · refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ (⁅K, B⁆ : Subgroup Ω).subgroupOf K := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end Comm

theorem eq_bot_of_commV_le_fixV {K : Subgroup (MulAut V)} (hK : Group.IsPerfect ↥K)
    (hKV : commV K ≤ fixV K) : K = ⊥ := by
  have hmem : ∀ k ∈ K, ∀ v : V, k v * v⁻¹ ∈ fixV K := fun k hk v =>
    hKV (Subgroup.subset_closure ⟨k, hk, v, rfl⟩)
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext v
  rw [MulAut.one_apply]
  let ψ : ↥K →* V :=
    { toFun := fun k => (k : MulAut V) v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have h1 : (a : MulAut V) ((b : MulAut V) v * v⁻¹) = (b : MulAut V) v * v⁻¹ :=
          hmem b b.2 v a a.2
        rw [map_mul, map_inv] at h1
        show (a : MulAut V) ((b : MulAut V) v) * v⁻¹ =
          ((a : MulAut V) v * v⁻¹) * ((b : MulAut V) v * v⁻¹)
        calc (a : MulAut V) ((b : MulAut V) v) * v⁻¹
            = ((a : MulAut V) ((b : MulAut V) v) * ((a : MulAut V) v)⁻¹) *
                ((a : MulAut V) v * v⁻¹) := by group
          _ = ((b : MulAut V) v * v⁻¹) * ((a : MulAut V) v * v⁻¹) := by rw [h1]
          _ = _ := mul_comm _ _ }
  have h1 := Abelianization.commutator_subset_ker ψ
  rw [Group.IsPerfect.commutator_eq_top] at h1
  have h2 : ψ ⟨g, hg⟩ = 1 := h1 (Subgroup.mem_top _)
  exact mul_inv_eq_one.1 h2

theorem apply_mem_commV {K : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (K : Set (MulAut V))) {u : V} (hu : u ∈ commV K) :
    g u ∈ commV K :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hg hu

theorem ne_bot_of_isQuasisimple {K : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K) :
    K ≠ ⊥ := by
  rintro rfl
  exact not_commute_of_isQuasisimple hK fun a ha b hb => by
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

theorem commSub_commV_ne_bot {K B : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K)
    (hKB : ⁅K, B⁆ = K) :
    commSub (commV K) B ≠ ⊥ := by
  intro hbot
  have hfix : commV K ≤ fixV B := commSub_eq_bot_iff.1 hbot
  have hle : ⁅K, B⁆ ≤ centSub (commV K) := by
    rw [Subgroup.commutator_le]
    intro k hk b hb u hu
    have h1 : b⁻¹ u = u := hfix hu b⁻¹ (B.inv_mem hb)
    have h2 : k⁻¹ u ∈ commV K := apply_mem_commV (Subgroup.le_normalizer (K.inv_mem hk)) hu
    have h3 : b (k⁻¹ u) = k⁻¹ u := hfix h2 b hb
    show (k * b * k⁻¹ * b⁻¹) u = u
    simp only [MulAut.mul_apply, h1, h3, MulAut.apply_inv_self]
  rw [hKB] at hle
  exact ne_bot_of_isQuasisimple hK
    (eq_bot_of_commV_le_fixV hK.1 fun u hu k hk => hle hk u hu)

theorem not_commV_le_fixV {K B : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K)
    (hKB : ⁅K, B⁆ = K) :
    ¬ commV B ≤ fixV K := by
  intro hBV
  set F := fixV K with hF
  have hcen : ∀ b ∈ B, b ∈ centSec ⊤ F := fun b hb =>
    ⟨mem_stabSub_top b, fun w _ => hBV (Subgroup.subset_closure ⟨b, hb, w, rfl⟩)⟩
  have hle : ⁅K, B⁆ ≤ centSec ⊤ F := by
    rw [Subgroup.commutator_le]
    intro k hk b hb
    have h1 : k * b * k⁻¹ ∈ centSec ⊤ F := by
      refine ⟨mem_stabSub_top _, fun w _ => ?_⟩
      have hf : b (k⁻¹ w) * (k⁻¹ w)⁻¹ ∈ F := (hcen b hb).2 _ trivial
      have e : (k * b * k⁻¹) w * w⁻¹ = k (b (k⁻¹ w) * (k⁻¹ w)⁻¹) := by
        simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [e, hf k hk]
      exact hf
    exact (centSec ⊤ F).mul_mem h1 ((centSec ⊤ F).inv_mem (hcen b hb))
  rw [hKB] at hle
  have hKV : commV K ≤ fixV K := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨k, hk, v, rfl⟩
    exact (hle hk).2 v trivial
  exact ne_bot_of_isQuasisimple hK (eq_bot_of_commV_le_fixV hK.1 hKV)

theorem le_of_fpf [Finite V] {c : MulAut V} {W M : Subgroup V} (hW : Nat.card W = 4)
    (hcW : ∀ w ∈ W, c w ∈ W) (hfix : ∀ w ∈ W, c w = w → w = 1) (hcM : ∀ m ∈ M, c m ∈ M)
    (hMW : M ⊓ W ≠ ⊥) : W ≤ M := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hMW
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hcw : c w ∈ M ⊓ W := ⟨hcM w hw.1, hcW w hw.2⟩
  have hcw1 : c w ≠ 1 := fun h => hw1' (c.injective (h.trans (map_one c).symm))
  have hne : c w ≠ w := fun h => hw1' (hfix w hw.2 h)
  have h3 : ¬ Nat.card ↥(M ⊓ W) ≤ 2 := fun h =>
    hne (B51Sum.eq_of_card_le_two h hcw hw hcw1 hw1')
  have hdvd : Nat.card ↥(M ⊓ W) ∣ 4 := hW ▸ Subgroup.card_dvd_of_le inf_le_right
  have hle4 : Nat.card ↥(M ⊓ W) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have h4 : Nat.card ↥(M ⊓ W) = 4 := by
    rcases (by omega : Nat.card ↥(M ⊓ W) = 3 ∨ Nat.card ↥(M ⊓ W) = 4) with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
  have heq : M ⊓ W = W := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h4, hW])
  exact heq ▸ inf_le_left

end CFSG.Quasithin.FFJImage
