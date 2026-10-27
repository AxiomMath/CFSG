module

public import CFSG.Quasithin.Background.InternalSecSumB
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.B1MoreElevenD

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.Assembly.LowTwoRank

section FFJ

variable {V : Type} [CommGroup V]

theorem isFFStarOffender_of_le {X Y A : Subgroup (MulAut V)} (h : IsFFStarOffender X A)
    (hAY : A ≤ Y) : IsFFStarOffender Y A :=
  ⟨hAY, h.2⟩

theorem ffJ_ffJ (X : Subgroup (MulAut V)) : ffJ (ffJ X) = ffJ X := by
  refine le_antisymm (B6.ffJ_le _) ?_
  show (⨆ (A : Subgroup (MulAut V)) (_ : IsFFStarOffender X A), A) ≤ ffJ (ffJ X)
  exact iSup₂_le fun A hA => B6.le_ffJ (isFFStarOffender_of_le hA (B6.le_ffJ hA))

theorem ffJ_ne_bot_of_isFFModule [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X : Subgroup (MulAut V)} (hFF : IsFFModule X) : ffJ X ≠ ⊥ := by
  obtain ⟨A, hA⟩ := ((B1_4_5 hV X).out 1 2).1 hFF
  intro h
  have := B6.le_ffJ hA
  rw [h, le_bot_iff] at this
  exact hA.2.1 this

theorem b51Hyp_ffJ_sup [Finite V] {K A : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K)
    (hS : SQTKGroup ↥K) (hA : IsFFStarOffender (Subgroup.normalizer (K : Set (MulAut V))) A)
    (hc : ∀ c : MulAut V, (∀ k ∈ K, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1) :
    B51Hyp (ffJ (K ⊔ A)) K ∧ A ≤ ffJ (K ⊔ A) := by
  set J := ffJ (K ⊔ A) with hJ
  have hKo := B1Red.isQuasisimple_to_open hK
  have hAn : A ≤ Subgroup.normalizer (K : Set (MulAut V)) := hA.1
  have hXn : K ⊔ A ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    sup_le (Subgroup.le_normalizer) hAn
  have hXK : ∀ x ∈ K ⊔ A, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (hXn hx) k).mp hk
  have hJX : J ≤ K ⊔ A := B6.ffJ_le _
  have hXJ : K ⊔ A ≤ Subgroup.normalizer (J : Set (MulAut V)) := B6.le_normalizer_ffJ _
  have hAJ : A ≤ J := B6.le_ffJ (isFFStarOffender_of_le hA le_sup_right)
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have hsq := B1Red.sq_mem_of_mem_sup hAn hA2
  have hKnil : ∀ P : Subgroup (MulAut V), K ≤ P → ¬ IsPGroup 2 ↥P := by
    intro P hKP hP
    have hnil := (hP.to_le hKP).isNilpotent
    have : Group.IsPerfect ↥K := ⟨hKo.1⟩
    have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hKo
    exact Group.IsPerfect.not_isNilpotent ↥K hnil
  have hKJ : K ≤ J := by
    by_contra hKJ
    have hcomm := B1Red.commute_of_normal_not_le hKo
      (fun n hn l hl => hXK n (hJX hn) l hl)
      (fun l hl n hn => (Subgroup.mem_normalizer_iff.mp
        (hXJ ((le_sup_left : K ≤ K ⊔ A) hl)) n).mp hn) hKJ
    apply hA.2.1
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.2
      (hc a (fun k hk => hcomm a (hAJ ha) k hk) 1 (by simpa using hA2 a ha))
  have hQ : pCoreOf 2 J = ⊥ := by
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 J) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
    have hQle : pCoreOf 2 J ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
    have hnot : ¬ K ≤ pCoreOf 2 J := fun h => hKnil _ h hQ2
    have hcomm := B1Red.commute_of_normal_not_le hKo
      (fun n hn l hl => hXK n (hJX (hQle hn)) l hl)
      (fun l hl n hn => B1Red.conj_mem_pCoreOf (hKJ hl) hn) hnot
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨e, he⟩ := hQ2 ⟨q, hq⟩
    exact Subgroup.mem_bot.2 (hc q (fun k hk => hcomm q hq k hk) e
      (by simpa using congrArg Subtype.val he))
  have h2 : ∀ y ∈ J, ∃ e : ℕ, y ^ 2 ^ e ∈ K := fun y hy => ⟨1, by simpa using hsq y (hJX hy)⟩
  have hF : quasithinGenFitting J = K :=
    quasithinGenFitting_eq_of_two_pow hKJ (fun y hy l hl => hXK y (hJX hy) l hl) hKo h2 hQ
  have hZ : centerOf J ≤ K := by
    rintro z ⟨hzJ, hzc⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    have hzm : z ^ m = 1 := by
      refine hc _ (fun l hl => ?_) k ?_
      · have h1 : Commute z l :=
          (Subgroup.mem_centralizer_iff.mp hzc l (hKJ hl)).symm
        exact (h1.pow_left m).eq
      · rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
    have hodd : Odd (orderOf z) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hzm)
    obtain ⟨e, he⟩ := h2 z hzJ
    exact mem_of_pow_mem_of_odd he hodd
  exact ⟨⟨by rw [hF, sup_eq_left.2 hZ], hK, hS, hKJ, hQ, (ffJ_ffJ _).symm⟩, hAJ⟩

end FFJ

section Sum

variable {V : Type} [CommGroup V] [Finite V] {K : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}

omit [Finite V] in
theorem le_commV_of_irr (hinv : ∀ k ∈ K, ∀ w ∈ W₁, k w ∈ W₁)
    (hirr : ∀ J : Subgroup V, J ≤ W₁ → (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₁)
    (hnt : ¬ W₁ ≤ fixV K) : W₁ ≤ commV K := by
  have hle : commSub W₁ K ≤ W₁ := commSub_le_of_invariant hinv
  have hcinv : ∀ k ∈ K, ∀ w ∈ commSub W₁ K, k w ∈ commSub W₁ K := by
    intro k hk w hw
    have hcl : commSub W₁ K ≤ (commSub W₁ K).comap (k : V ≃* V).toMonoidHom := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, u, hu, rfl⟩
      show k (x u * u⁻¹) ∈ commSub W₁ K
      have e : k (x u * u⁻¹) = (k * x * k⁻¹) (k u) * (k u)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [e]
      exact Subgroup.subset_closure ⟨_, K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk), k u,
        hinv k hk u hu, rfl⟩
    exact hcl hw
  rcases hirr _ hle hcinv with h | h
  · exact absurd (commSub_eq_bot_iff.1 h) hnt
  · rw [← h, commV_eq_commSub]
    exact commSub_mono le_top le_rfl

theorem not_isFFModule_normalizer_of_sum (h51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1)
    (hK : CFSG.IsQuasisimple ↥K) (hS : SQTKGroup ↥K) (hsum : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥)
    (hinv₁ : ∀ k ∈ K, ∀ w ∈ W₁, k w ∈ W₁) (hinv₂ : ∀ k ∈ K, ∀ w ∈ W₂, k w ∈ W₂)
    (hirr₁ : ∀ J : Subgroup V, J ≤ W₁ → (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₁)
    (hirr₂ : ∀ J : Subgroup V, J ≤ W₂ → (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₂)
    (hnt₁ : ¬ W₁ ≤ fixV K) (hnt₂ : ¬ W₂ ≤ fixV K) (hnoniso : ¬ SecIsoL K W₁ ⊥ W₂ ⊥)
    (hLn : ∀ n : ℕ, (n = 4 ∨ n = 5) →
      ∀ π : ↥(StatedSL n (ZMod 2)) →* ↥K, ¬ Function.Surjective π) :
    ¬ IsFFModule (Subgroup.normalizer (K : Set (MulAut V))) := by
  have hW₁ : W₁ ≠ ⊥ := fun h => hnt₁ (h ▸ bot_le)
  have hW₂ : W₂ ≠ ⊥ := fun h => hnt₂ (h ▸ bot_le)
  have hc : ∀ c : MulAut V, (∀ k ∈ K, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1 :=
    fun c hcK e hce => eq_one_of_commute_of_sum hsum hinf hinv₁ hinv₂ hV hirr₁ hirr₂ hW₁ hW₂
      hnoniso hcK hce
  intro hFF
  obtain ⟨A, hA⟩ := ((B1_4_5 hV _).out 1 2).1 hFF
  obtain ⟨hB51, -⟩ := b51Hyp_ffJ_sup hK hS hA hc
  have h3 := (h51 V hV _ K hB51).2.2.1
  have hU : commV K = ⊤ := by
    rw [eq_top_iff, ← hsum]
    exact sup_le (le_commV_of_irr hinv₁ hirr₁ hnt₁) (le_commV_of_irr hinv₂ hirr₂ hnt₂)
  have hfix : fixV K = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : v ∈ W₁ ⊔ W₂ := by rw [hsum]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv'
    have hfixa : ∀ k ∈ K, k a = a ∧ k b = b := by
      intro k hk
      have h1 : k a * k b = a * b := by rw [← map_mul]; exact hv k hk
      exact eq_of_mul_eq_mul hinf (hinv₁ k hk a ha) ha (hinv₂ k hk b hb) hb h1
    have hFa : fixV K ⊓ W₁ = ⊥ := by
      rcases hirr₁ (fixV K ⊓ W₁) inf_le_right (fun k hk w hw =>
        ⟨fun x hx => by rw [hw.1 k hk, hw.1 x hx], hinv₁ k hk w hw.2⟩) with h | h
      · exact h
      · exact (hnt₁ (by rw [← h]; exact inf_le_left)).elim
    have hFb : fixV K ⊓ W₂ = ⊥ := by
      rcases hirr₂ (fixV K ⊓ W₂) inf_le_right (fun k hk w hw =>
        ⟨fun x hx => by rw [hw.1 k hk, hw.1 x hx], hinv₂ k hk w hw.2⟩) with h | h
      · exact h
      · exact (hnt₂ (by rw [← h]; exact inf_le_left)).elim
    have ha1 : a ∈ fixV K ⊓ W₁ := ⟨fun k hk => (hfixa k hk).1, ha⟩
    have hb1 : b ∈ fixV K ⊓ W₂ := ⟨fun k hk => (hfixa k hk).2, hb⟩
    rw [hFa, Subgroup.mem_bot] at ha1
    rw [hFb, Subgroup.mem_bot] at hb1
    rw [ha1, hb1, one_mul]
    exact Subgroup.one_mem _
  have hZ : fixV K ⊓ commV K = ⊥ := by rw [hfix, bot_inf_eq]
  unfold B51Part3 at h3
  rw [hZ, hU] at h3
  rcases h3 with hhom | ⟨n, hn, π, U₁, U₂, -, hR, -⟩
  · have hirrSec : ∀ W : Subgroup V, W ≠ ⊥ →
        (∀ J : Subgroup V, J ≤ W → (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W) →
        (∀ k ∈ K, ∀ w ∈ W, k w ∈ W) →
        (⊥ ≤ W ∧ W ≤ ⊤ ∧ XMod.IsInv ↥K W ∧ XMod.IsIrrSec ↥K ⊥ W) := by
      intro W hW hirr hinv
      refine ⟨bot_le, le_top, fun a w hw => hinv a a.2 w hw, bot_lt_iff_ne_bot.2 hW,
        fun J hJ _ hJW => hirr J hJW fun k hk w hw => hJ ⟨k, hk⟩ w hw⟩
    exact hnoniso (hhom.2 W₁ W₂ (hirrSec W₁ hW₁ hirr₁ hinv₁) (hirrSec W₂ hW₂ hirr₂ hinv₂))
  · exact hLn n hn π hR.1

end Sum

end CFSG.Quasithin.InternalSec
