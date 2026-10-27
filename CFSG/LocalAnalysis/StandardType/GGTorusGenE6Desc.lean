module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Odd
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHolds

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
open CFSG.StandardType.U63TB

private lemma twoSub_eq_one_of_odd {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : N ≤ Subgroup.center G) {z : G}
    (hz : z ∈ twoSub N hN) (hodd : Odd (orderOf z)) : z = 1 := by
  rw [mem_twoSub] at hz
  have hdvd : orderOf z ∣ 2 ^ Nat.card G := orderOf_dvd_of_pow_eq_one hz.2
  have hcop : Nat.Coprime (orderOf z) (2 ^ Nat.card G) :=
    (hodd.coprime_two_right).pow_right (Nat.card G)
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)

private lemma twoSub_eq_one_of_odd_pow {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : N ≤ Subgroup.center G) {z : G} {m : ℕ}
    (hz : z ∈ twoSub N hN) (hm : Odd m) (hzm : z ^ m = 1) : z = 1 :=
  twoSub_eq_one_of_odd hN hz (hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hzm))

private lemma odd_orderOf_mul_of_commute {G : Type} [Group G] {s t : G}
    (h : Commute s t) (hs : Odd (orderOf s)) (ht : Odd (orderOf t)) :
    Odd (orderOf (s * t)) :=
  (Nat.odd_mul.mpr ⟨hs, ht⟩).of_dvd_nat h.orderOf_mul_dvd_mul_orderOf

private lemma odd_three_pow (k : ℕ) : Odd (3 ^ k) := by
  induction k with
  | zero => exact odd_one
  | succ k ih => rw [pow_succ]; exact ih.mul (by decide : Odd 3)

private theorem strong_descent {R : Type} [Group R] {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAle : A ≤ presZ (twoSub ψ.ker hker))
    (hbar : GGE6ThreeStrongData (psi1 hker).ker (redSub hker hAle).range) :
    GGE6ThreeStrongData ψ.ker A := by
  classical
  let Z2 : Subgroup L' := twoSub ψ.ker hker
  haveI : Z2.Normal := twoSub_normal hker
  obtain ⟨Tb, wb, hb⟩ := hbar
  obtain ⟨hCommTb, hZoddTb, hFixTb, hCobTb, hTmaxTb, hGenTb⟩ := hb
  have hPcomm : ∀ s t : L', (s : L' ⧸ Z2) ∈ Tb → (t : L' ⧸ Z2) ∈ Tb →
      Odd (orderOf t) → s * t = t * s := by
    intro s t hs ht htodd
    have hst : (s : L' ⧸ Z2) * (t : L' ⧸ Z2) = (t : L' ⧸ Z2) * (s : L' ⧸ Z2) :=
      hCommTb _ hs _ ht
    have hc : s * t * s⁻¹ * t⁻¹ ∈ Z2 := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hst]
      group
    have hct : Commute (s * t * s⁻¹ * t⁻¹) t :=
      (commute_iff_eq _ _).mpr ((Subgroup.mem_center_iff.mp (twoSub_le_center hker hc) t).symm)
    have h1 : (s * t * s⁻¹) ^ orderOf t = 1 := by
      rw [show s * t * s⁻¹ = (MulAut.conj s) t from (MulAut.conj_apply s t).symm, ← map_pow,
        pow_orderOf_eq_one, map_one]
    have h2 : (s * t * s⁻¹ * t⁻¹) * t = s * t * s⁻¹ := by group
    have hcm : (s * t * s⁻¹ * t⁻¹) ^ orderOf t = 1 := by
      have hmul : ((s * t * s⁻¹ * t⁻¹) * t) ^ orderOf t =
          (s * t * s⁻¹ * t⁻¹) ^ orderOf t := by
        rw [hct.mul_pow, pow_orderOf_eq_one, mul_one]
      rw [← hmul, h2, h1]
    have hc1 : s * t * s⁻¹ * t⁻¹ = 1 := twoSub_eq_one_of_odd_pow hker hc htodd hcm
    have hconj : s * t * s⁻¹ = t := by rw [← h2, hc1, one_mul]
    have := congrArg (fun x => x * s) hconj
    simpa using this
  let S : Subgroup L' :=
    { carrier := {x | (x : L' ⧸ Z2) ∈ Tb ∧ Odd (orderOf x)}
      one_mem' := ⟨by rw [QuotientGroup.mk_one]; exact Tb.one_mem, by rw [orderOf_one]; decide⟩
      mul_mem' := by
        rintro s t ⟨hs, hso⟩ ⟨ht, hto⟩
        refine ⟨?_, ?_⟩
        · rw [QuotientGroup.mk_mul]; exact Tb.mul_mem hs ht
        · exact odd_orderOf_mul_of_commute ((commute_iff_eq _ _).mpr (hPcomm s t hs ht hto)) hso hto
      inv_mem' := by
        rintro s ⟨hs, hso⟩
        refine ⟨?_, ?_⟩
        · rw [QuotientGroup.mk_inv]; exact Tb.inv_mem hs
        · rwa [orderOf_inv] }
  have hSmem : ∀ x, x ∈ S ↔ (x : L' ⧸ Z2) ∈ Tb ∧ Odd (orderOf x) := fun _ => Iff.rfl
  have hex : ∀ i : Fin 6, ∃ n : L', (n : L' ⧸ Z2) = wb i ∧
      ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹ := by
    intro i
    exact exists_lift_W (ψ := ψ) hker hA hAle (fun a₁ ha₁ =>
      ⟨(hCobTb i a₁ ha₁).2, fun a₁' ha₁' => hFixTb a₁' ha₁' _ (hCobTb i a₁ ha₁).1⟩)
  choose w hw using hex
  have hCommS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    exact hPcomm s t ((hSmem s).mp hs).1 ((hSmem t).mp ht).1 ((hSmem t).mp ht).2
  have hZoddS : ∀ z ∈ ψ.ker, Odd (orderOf z) → z ∈ S := by
    intro z hz hzo
    refine (hSmem z).mpr ⟨?_, hzo⟩
    have hzq : (z : L' ⧸ Z2) ∈ (psi1 hker).ker := (mem_ker_psi1 hker).mpr hz
    have hdvd : orderOf (z : L' ⧸ Z2) ∣ orderOf z := by
      simpa [QuotientGroup.mk'_apply] using orderOf_map_dvd (QuotientGroup.mk' Z2) z
    exact hZoddTb _ hzq (hzo.of_dvd_nat hdvd)
  have hFixS : ∀ a ∈ A, ∀ t ∈ S, a t = t := by
    intro a ha t ht
    have hatq : ((a : MulAut L') t : L' ⧸ Z2) = (t : L' ⧸ Z2) := by
      rw [← redSub_mk hker hAle ⟨a, ha⟩ t]
      exact hFixTb (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ (t : L' ⧸ Z2) ((hSmem t).mp ht).1
    have hatS : (a : MulAut L') t ∈ S := by
      refine (hSmem _).mpr ⟨?_, ?_⟩
      · rw [hatq]; exact ((hSmem t).mp ht).1
      · rw [show orderOf ((a : MulAut L') t) = orderOf t from
          MulEquiv.orderOf_eq (a : MulAut L') t]
        exact ((hSmem t).mp ht).2
    have hz : (a : MulAut L') t * t⁻¹ ∈ Z2 := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hatq, mul_inv_cancel]
    have hz1 : (a : MulAut L') t * t⁻¹ = 1 :=
      twoSub_eq_one_of_odd hker hz ((hSmem _).mp (S.mul_mem hatS (S.inv_mem ht))).2
    have := congrArg (fun x => x * t) hz1
    simpa using this
  have hCobS : ∀ i, ∀ a ∈ A, w i * (a (w i))⁻¹ ∈ S ∧ (w i * (a (w i))⁻¹) ^ 3 = 1 := by
    intro i a ha
    have hcube : (w i * (a (w i))⁻¹) ^ 3 = 1 := ((hw i).2 a ha).1
    refine ⟨(hSmem _).mpr ⟨?_, ?_⟩, hcube⟩
    · have haq : ((a (w i) : L') : L' ⧸ Z2) = redSub hker hAle ⟨a, ha⟩ (wb i) := by
        rw [← (hw i).1]
        exact (redSub_mk hker hAle ⟨a, ha⟩ (w i)).symm
      have h1 : ((w i * (a (w i))⁻¹ : L') : L' ⧸ Z2) =
          wb i * (redSub hker hAle ⟨a, ha⟩ (wb i))⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (hw i).1, haq]
      rw [h1]
      exact (hCobTb i (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
    · exact (show Odd 3 by decide).of_dvd_nat (orderOf_dvd_of_pow_eq_one hcube)
  have hTmaxS : ∀ c : L', (∀ a ∈ A, a c = c) → Odd (orderOf c) → c ∈ S := by
    intro c hc hodd
    refine (hSmem c).mpr ⟨?_, hodd⟩
    apply hTmaxTb
    · intro ab hab
      obtain ⟨a, rfl⟩ := hab
      rw [redSub_mk hker hAle a]
      rw [hc a.1 a.2]
    · exact hodd.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' Z2) c)
  refine ⟨S, w, hCommS, hZoddS, hFixS, hCobS, hTmaxS, ?_⟩
  intro a ha hane J hJ c hcS hc3
  let ab : (redSub hker hAle).range := ⟨redSub hker hAle ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩
  have hne : (ab : MulAut (L' ⧸ Z2)) ≠ 1 := by
    intro hab1
    have h3 : (a : MulAut L') = 1 := by
      have h2 : (⟨a, ha⟩ : A) = 1 := by
        apply redSub_injective hker hAle hperf
        simpa [ab] using hab1
      simpa using congrArg Subtype.val h2
    exact hane h3
  let Jb : Subgroup (L' ⧸ Z2) := J.map (QuotientGroup.mk' Z2)
  have hJb : IsComponentOf Jb (ggFix (ab : MulAut (L' ⧸ Z2))) :=
    isComponentOf_map_ggFix_of_central (ψ := QuotientGroup.mk' Z2)
      (QuotientGroup.mk'_surjective Z2)
      (by rw [QuotientGroup.ker_mk']; exact twoSub_le_center hker)
      (fun l => redSub_mk hker hAle ⟨a, ha⟩ l) hJ
  have hcbarTb : (c : L' ⧸ Z2) ∈ Tb := ((hSmem c).mp hcS).1
  have hcbar3 : ∃ k : ℕ, (c : L' ⧸ Z2) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hc3
    exact ⟨k, by
      change (QuotientGroup.mk' Z2 c) ^ 3 ^ k = 1
      rw [← map_pow, hk, map_one]⟩
  let G : Subgroup L' := Subgroup.closure (⋃ n ∈ (Subgroup.closure (Set.range w) : Set L'),
      (fun s => n * s * n⁻¹) '' {s : L' | s ∈ J ∧ s ∈ S ∧ ∃ k : ℕ, s ^ 3 ^ k = 1})
  let Gb : Subgroup (L' ⧸ Z2) := Subgroup.closure
      (⋃ n ∈ (Subgroup.closure (Set.range wb) : Set (L' ⧸ Z2)),
      (fun s => n * s * n⁻¹) '' {s : L' ⧸ Z2 | s ∈ Jb ∧ s ∈ Tb ∧ ∃ k : ℕ, s ^ 3 ^ k = 1})
  have hcbarG : (c : L' ⧸ Z2) ∈ Gb :=
    hGenTb (ab : MulAut (L' ⧸ Z2)) ab.2 hne Jb hJb (c : L' ⧸ Z2) hcbarTb hcbar3
  have hmapW : (Subgroup.closure (Set.range w)).map (QuotientGroup.mk' Z2) =
      Subgroup.closure (Set.range wb) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, hy⟩
      refine ⟨i, ?_⟩
      rw [← hy]
      exact ((hw i).1).symm
    · rintro ⟨i, rfl⟩
      exact ⟨w i, ⟨i, rfl⟩, (hw i).1⟩
  have hGb_le : Gb ≤ G.map (QuotientGroup.mk' Z2) := by
    refine (Subgroup.closure_le (G.map (QuotientGroup.mk' Z2))).mpr (fun x hx => ?_)
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop] at hx
    rcases hx with ⟨nb, hnb, sb, hsb, hxeq⟩
    rcases hsb with ⟨hsbJb, hsbTb, hsb3⟩
    rw [← hxeq]
    have hnb' : nb ∈ (Subgroup.closure (Set.range w)).map (QuotientGroup.mk' Z2) := by
      rwa [hmapW]
    obtain ⟨n, hn, hnq⟩ := hnb'
    obtain ⟨sJ, hsJ, hsJmk⟩ := hsbJb
    obtain ⟨k0, hk0⟩ := hsb3
    have hrodd : Odd (orderOf sb) :=
      (odd_three_pow k0).of_dvd_nat (orderOf_dvd_of_pow_eq_one hk0)
    have hsInt : ∃ s : L', s ∈ J ∧ (s : L' ⧸ Z2) = sb ∧ s ∈ S ∧ ∃ k, s ^ 3 ^ k = 1 := by
      by_cases hr : orderOf sb = 1
      · refine ⟨1, J.one_mem, ?_, S.one_mem, ⟨0, by simp⟩⟩
        rw [QuotientGroup.mk_one, orderOf_eq_one_iff.mp hr]
      · have hne0 : orderOf sb ≠ 0 := by
          rintro h0; rw [h0] at hrodd; obtain ⟨k, hk⟩ := hrodd; omega
        have hr1 : 1 < orderOf sb := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hne0, hr⟩
        have hcop : Nat.Coprime (2 ^ Nat.card L') (orderOf sb) :=
          hrodd.coprime_two_left.pow_left (Nat.card L')
        obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr1
        have hsJr : (sJ ^ orderOf sb) ^ (2 ^ Nat.card L') = 1 := by
          have hz : sJ ^ orderOf sb ∈ Z2 := by
            rw [← QuotientGroup.eq_one_iff]
            change (QuotientGroup.mk' Z2) (sJ ^ orderOf sb) = 1
            rw [map_pow, hsJmk, pow_orderOf_eq_one]
          exact ((mem_twoSub hker).mp hz).2
        have hsJpow : (sJ ^ (2 ^ Nat.card L' * u)) ^ orderOf sb = 1 := by
          rw [← pow_mul, show (2 ^ Nat.card L' * u) * orderOf sb =
              (2 ^ Nat.card L' * orderOf sb) * u by ring, pow_mul,
            show 2 ^ Nat.card L' * orderOf sb = orderOf sb * 2 ^ Nat.card L' by ring,
            pow_mul, hsJr, one_pow]
        have hpow : sb ^ (2 ^ Nat.card L' * u) = sb := by
          rw [← pow_mod_orderOf sb (2 ^ Nat.card L' * u), hu, pow_one]
        have hsmk : ((sJ ^ (2 ^ Nat.card L' * u) : L') : L' ⧸ Z2) = sb := by
          change (QuotientGroup.mk' Z2) (sJ ^ (2 ^ Nat.card L' * u)) = sb
          rw [map_pow, hsJmk, hpow]
        have hsodd : Odd (orderOf (sJ ^ (2 ^ Nat.card L' * u))) :=
          hrodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hsJpow)
        refine ⟨sJ ^ (2 ^ Nat.card L' * u), J.pow_mem hsJ _, hsmk, ?_, ?_⟩
        · exact (hSmem _).mpr ⟨by rw [hsmk]; exact hsbTb, hsodd⟩
        · have hdvd : orderOf (sJ ^ (2 ^ Nat.card L' * u)) ∣ 3 ^ k0 :=
            dvd_trans (orderOf_dvd_of_pow_eq_one hsJpow) (orderOf_dvd_of_pow_eq_one hk0)
          exact ⟨k0, (orderOf_dvd_iff_pow_eq_one).mp hdvd⟩
    obtain ⟨s, hsJ, hsmk, hsS, hs3⟩ := hsInt
    refine ⟨n * s * n⁻¹, ?_, ?_⟩
    · apply Subgroup.subset_closure
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hn, ?_⟩
      exact Set.mem_image_of_mem (fun s => n * s * n⁻¹) ⟨hsJ, hsS, hs3⟩
    · change (QuotientGroup.mk' Z2) (n * s * n⁻¹) = nb * sb * nb⁻¹
      rw [map_mul, map_mul, map_inv, hnq, show (QuotientGroup.mk' Z2) s = sb from hsmk]
  have hcbarGmap : (c : L' ⧸ Z2) ∈ G.map (QuotientGroup.mk' Z2) := hGb_le hcbarG
  obtain ⟨g, hgG, hgmk⟩ := hcbarGmap
  have hz : g⁻¹ * c ∈ Z2 := QuotientGroup.eq.mp hgmk
  have hzN : (g⁻¹ * c) ^ (2 ^ Nat.card L') = 1 := ((mem_twoSub hker).mp hz).2
  have hcomm : Commute g (g⁻¹ * c) :=
    (commute_iff_eq g _).mpr (Subgroup.mem_center_iff.mp (twoSub_le_center hker hz) g)
  have hcomp : c ^ (2 ^ Nat.card L') = g ^ (2 ^ Nat.card L') := by
    have hcz : c = g * (g⁻¹ * c) := by group
    rw [hcz, hcomm.mul_pow, hzN, mul_one]
  by_cases hc1 : c = 1
  · subst hc1; exact G.one_mem
  · have hodd : Odd (orderOf c) := by
      obtain ⟨k, hk⟩ := hc3
      exact (odd_three_pow k).of_dvd_nat (orderOf_dvd_of_pow_eq_one hk)
    have hne0 : orderOf c ≠ 0 := by
      rintro h0; rw [h0] at hodd; obtain ⟨k, hk⟩ := hodd; omega
    have ho1 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.mp h)
    have hr1 : 1 < orderOf c := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hne0, ho1⟩
    have hcop : Nat.Coprime (2 ^ Nat.card L') (orderOf c) :=
      hodd.coprime_two_left.pow_left (Nat.card L')
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr1
    have hpowc : c ^ (2 ^ Nat.card L' * u) = c := by
      rw [← pow_mod_orderOf c (2 ^ Nat.card L' * u), hu, pow_one]
    have hc_eq : c = (c ^ (2 ^ Nat.card L')) ^ u := by rw [← pow_mul, hpowc]
    have hgpow : g ^ (2 ^ Nat.card L') ∈ G := G.pow_mem hgG _
    rw [hc_eq, hcomp]
    exact G.pow_mem hgpow u

theorem strongSCr_of_good {R : Type} [Group R] (hAL : GGAbelianLift) (D : FrameData R) (hD : D.Good)
    (hRG : GGE6ThreeRGen D) (hcov : CoverOdd R) (I : Set (MulAut R)) (hI : (D.H : Set (MulAut R)) = I)
    (hM4 : GGE6ThreeCoverCommSCr R I) : GGE6ThreeStrongSCr R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h5 hsc
  haveI : Finite R := Finite.of_surjective ψ hψ
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hD.center
  let ρ : MulAut L' →* MulAut R := BstarDesc.descAut hψ hZ
  have hρ : ∀ a l, ρ a (ψ l) = ψ (a l) := fun a l => BstarDesc.descAut_apply hψ hZ a l
  have hρinj : Function.Injective ρ := BstarDesc.descAut_injective hψ hZ hperf
  have hAH : ∀ a ∈ A, ρ a ∈ D.H := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hρφ : ρ a = φ := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hρ, hφ]
    have hφH : φ ∈ (D.H : Set (MulAut R)) := by rw [hI]; exact hφI
    rw [hρφ]
    exact hφH
  obtain ⟨γ, hγH, hγ⟩ := exists_align D hD.shape hρinj hA h5 hAH
  let ψ' : L' →* R := γ.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := γ.surjective.comp hψ
  have hkerEq : ψ'.ker = ψ.ker := by
    ext l
    simp [ψ', MonoidHom.mem_ker]
  have hker' : ψ'.ker ≤ Subgroup.center L' := hkerEq ▸ hker
  have hZ' : ψ'.ker = Subgroup.center L' := hkerEq ▸ hZ
  let ρ' : MulAut L' →* MulAut R := BstarDesc.descAut hψ' hZ'
  have hρ' : ∀ a l, ρ' a (ψ' l) = ψ' (a l) := fun a l => BstarDesc.descAut_apply hψ' hZ' a l
  have hρ'eq : ∀ a, ρ' a = γ * ρ a * γ⁻¹ := by
    intro a
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ := hψ' r
    rw [hρ']
    simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply,
      MulAut.inv_apply_self, hρ, map_mul]
  have hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ'.ker hker') := fun a ha =>
    U63TB.mem_presZ_of_ker hker' fun z hz =>
      U63TB.preserves_ker (I := Set.univ) ⟨ρ' a, Set.mem_univ _, fun l => hρ' a l⟩ hz
  have hψb : Function.Surjective (U63TB.psi1 hker') := U63TB.psi1_surjective hker' hψ'
  have hkerb := U63TB.psi1_ker_central hker'
  have hperfb := U63TB.commutator_quot hker' hperf
  have hodd := U63TB.odd_card_ker_psi1 hker'
  have hcardb : Nat.card (U63TB.psi1 hker').ker = 1 ∨ Nat.card (U63TB.psi1 hker').ker = 3 := by
    obtain ⟨k, hk⟩ := hcov _ (U63TB.psi1 hker') hψb hkerb hperfb
    have h3 : Nat.card (U63TB.psi1 hker').ker ∣ 3 :=
      (Nat.Coprime.pow_right k hodd.coprime_two_right).dvd_of_dvd_mul_left hk
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    exacts [Or.inl h, Or.inr h]
  have hZb := BstarDesc.ker_eq_center hψb hkerb hD.center
  let ρb := BstarDesc.descAut hψb hZb
  have hρb : ∀ a l, ρb a (U63TB.psi1 hker' l) = U63TB.psi1 hker' (a l) := fun a l =>
    BstarDesc.descAut_apply hψb hZb a l
  have hρbinj := BstarDesc.descAut_injective hψb hZb hperfb
  have hAb := U63TB.isElemAbelian_range_redSub hker' hAle hA
  have hscb := U63TB.selfCent_quot hker' hA hAle hsc
  have halb : ∀ ab ∈ (U63TB.redSub hker' hAle).range, ρb ab ∈ D.diag.range := by
    rintro _ ⟨a, rfl⟩
    have hab : ρb (U63TB.redSub hker' hAle a) = ρ' a.1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨lb, rfl⟩ := hψb r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
      rw [hρb, U63TB.psi1_mk, U63TB.redSub_mk, U63TB.psi1_mk, hρ']
    rw [hab, hρ'eq]
    exact hγ a.1 a.2
  have hAI' : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ' l) = ψ' (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hφH : φ ∈ (D.H : Set (MulAut R)) := by rw [hI]; exact hφI
    refine ⟨γ * φ * γ⁻¹, ?_, fun l => ?_⟩
    · have : γ * φ * γ⁻¹ ∈ (D.H : Set (MulAut R)) :=
        D.H.mul_mem (D.H.mul_mem hγH hφH) (D.H.inv_mem hγH)
      rwa [hI] at this
    · show (γ * φ * γ⁻¹) (γ (ψ l)) = γ (ψ (a l))
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hφ l]
  have hAIb : ∀ ab ∈ (U63TB.redSub hker' hAle).range, ∃ φ ∈ I,
      ∀ l₁ : L' ⧸ U63TB.twoSub ψ'.ker hker',
        φ (U63TB.psi1 hker' l₁) = U63TB.psi1 hker' (ab l₁) :=
    U63TB.redSub_hAI hker' hAle hAI'
  have h5b : 3 ^ 5 ≤ Nat.card (U63TB.redSub hker' hAle).range := by
    rw [U63TB.card_range_redSub hker' hAle hperf]; exact h5
  have hbar := strong_odd_of_good D hAL hD hRG hM4 hψb hkerb hperfb hcardb hρb hρbinj
    hAb hscb halb hAIb h5b
  have hmodel := strong_descent hker' hperf hA hAle hbar
  rwa [hkerEq] at hmodel

end CFSG.StandardType.E6ThreeModel
