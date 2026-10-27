module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Q
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4dProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Hering611
open CFSG.GorensteinWalter (PSL2)

variable {G : Type} [Group G] [Finite G]

theorem commutes {L' Q : Subgroup G} {d b s : G}
    (e : L' ⧸ aschbacherSolvableCore 3 L' ≃* PSL2 (GaloisField 3 6))
    (hQ2 : IsPGroup 2 Q) (hQN : Q ≤ Subgroup.normalizer (L' : Set G))
    (hfaith : ∀ q ∈ Q, ∀ hq : q ∈ Subgroup.normalizer (L' : Set G),
      Sec12.thetaBarAct L' ⟨q, hq⟩ = 1 → q = 1)
    (hdN : d ∈ Subgroup.normalizer (L' : Set G)) (hd3 : d ^ 3 = 1) (hbL : b ∈ L')
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hdb : d * b = b * d)
    (hdQ : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hbQ : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hsQ : s ∈ Q)
    (hsd : d * s = s * d) (hsb : b * s ≠ s * b) : ∀ q ∈ Q, d * q = q * d := by
  have hK : Nat.card (GaloisField 3 6) = 3 ^ 6 := GaloisField.card 3 6 (by norm_num)
  have hK3 : ringChar (GaloisField 3 6) = 3 := ringChar.eq (GaloisField 3 6) 3
  have hcongr : ∀ y : L' ⧸ aschbacherSolvableCore 3 L',
      MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
    intro y
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  let ψ : Subgroup.normalizer (L' : Set G) →* MulAut (PSL2 (GaloisField 3 6)) :=
    (MulAut.congr e).toMonoidHom.comp (Sec12.thetaBarAct L')
  have hker : ∀ c : G, ∀ hc : c ∈ Q, ψ ⟨c, hQN hc⟩ = 1 → c = 1 := by
    intro c hc h
    have h' : MulAut.congr e (Sec12.thetaBarAct L' ⟨c, hQN hc⟩) = 1 := h
    exact hfaith c hc (hQN hc) ((MulEquiv.map_eq_one_iff (MulAut.congr e)).mp h')
  have hcomm_ker : ∀ x y : Subgroup.normalizer (L' : Set G),
      ψ x * ψ y = ψ y * ψ x → ψ (x * y * x⁻¹ * y⁻¹) = 1 := by
    intro x y h
    simp only [map_mul, map_inv]
    rw [h]
    group
  set u : PSL2 (GaloisField 3 6) :=
    e (QuotientGroup.mk' (aschbacherSolvableCore 3 L') (⟨b, hbL⟩ : L')) with hu_def
  have hψb : ψ ⟨b, Subgroup.le_normalizer hbL⟩ = MulAut.conj u := by
    show MulAut.congr e (Sec12.thetaBarAct L' ⟨b, Subgroup.le_normalizer hbL⟩) = MulAut.conj u
    rw [Sec12.thetaBarAct_of_mem hbL, hcongr]
  have hu3 : u ^ 3 = 1 := by
    have hx3 : (⟨b, hbL⟩ : L') ^ 3 = 1 := Subtype.ext (by simp [hb3])
    rw [hu_def, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hu1 : u ≠ 1 := by
    intro hu
    have hπ : QuotientGroup.mk' (aschbacherSolvableCore 3 L') (⟨b, hbL⟩ : L') = 1 :=
      e.injective (by rw [map_one]; exact hu)
    have hxθ : (⟨b, hbL⟩ : L') ∈ aschbacherSolvableCore 3 L' :=
      (QuotientGroup.eq_one_iff _).mp hπ
    have hbT : b ∈ inSubgroup (aschbacherSolvableCore 3) L' :=
      Subgroup.mem_map_of_mem L'.subtype hxθ
    have ht3 : (⟨b, hbT⟩ : inSubgroup (aschbacherSolvableCore 3) L') ^ 3 = 1 :=
      Subtype.ext (by simp [hb3])
    have ht1 : (⟨b, hbT⟩ : inSubgroup (aschbacherSolvableCore 3) L') ≠ 1 :=
      fun h => hb1 (congrArg Subtype.val h)
    have hdvd := orderOf_dvd_natCard (⟨b, hbT⟩ : inSubgroup (aschbacherSolvableCore 3) L')
    rw [orderOf_eq_prime ht3 ht1] at hdvd
    exact Sec11.not_three_dvd_card_inSubgroup_theta L' hdvd
  set Q' : Subgroup (MulAut (PSL2 (GaloisField 3 6))) :=
    (Q.subgroupOf (Subgroup.normalizer (L' : Set G))).map ψ with hQ'_def
  have hQ'2 : IsPGroup 2 Q' :=
    (hQ2.comap_subtype (K := Subgroup.normalizer (L' : Set G))).map ψ
  have hconjQ : ∀ n : Subgroup.normalizer (L' : Set G),
      (∀ x ∈ Q, (n : G) * x * (n : G)⁻¹ ∈ Q) → ∀ q ∈ Q', ψ n * q * (ψ n)⁻¹ ∈ Q' := by
    intro n hn q hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr
      (hn x (Subgroup.mem_subgroupOf.mp hx)))
  set δ : MulAut (PSL2 (GaloisField 3 6)) := ψ ⟨d, hdN⟩ with hδ_def
  have hδ3 : δ ^ 3 = 1 := by
    have hd3' : (⟨d, hdN⟩ : Subgroup.normalizer (L' : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simp [hd3])
    rw [hδ_def, ← map_pow, hd3', map_one]
  have hδQ : ∀ q ∈ Q', δ * q * δ⁻¹ ∈ Q' :=
    hconjQ ⟨d, hdN⟩ (fun x hx => hdQ x hx)
  have hβQ : ∀ q ∈ Q', MulAut.conj u * q * (MulAut.conj u)⁻¹ ∈ Q' := by
    rw [← hψb]
    exact hconjQ ⟨b, Subgroup.le_normalizer hbL⟩ (fun x hx => hbQ x hx)
  have hδβ : δ * MulAut.conj u = MulAut.conj u * δ := by
    rw [← hψb, hδ_def, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdb
  have hsN : s ∈ Subgroup.normalizer (L' : Set G) := hQN hsQ
  set s' : MulAut (PSL2 (GaloisField 3 6)) := ψ ⟨s, hsN⟩ with hs'_def
  have hsQN : (⟨s, hsN⟩ : Subgroup.normalizer (L' : Set G)) ∈ Q.subgroupOf
      (Subgroup.normalizer (L' : Set G)) := Subgroup.mem_subgroupOf.mpr hsQ
  have hs'Q : s' ∈ Q' := Subgroup.mem_map_of_mem ψ hsQN
  have hsδ : δ * s' = s' * δ := by
    rw [hδ_def, hs'_def, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hsd
  have hsβ : MulAut.conj u * s' ≠ s' * MulAut.conj u := by
    intro h
    rw [← hψb] at h
    have hw1 := hcomm_ker ⟨b, Subgroup.le_normalizer hbL⟩ ⟨s, hsN⟩ h
    have hwQ : b * s * b⁻¹ * s⁻¹ ∈ Q := Q.mul_mem (hbQ s hsQ) (Q.inv_mem hsQ)
    have hw : b * s * b⁻¹ * s⁻¹ = 1 := hker _ hwQ hw1
    exact hsb (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hw))
  have hcomm := theoremQ (K := GaloisField 3 6) hK hK3 hu3 hu1 hδ3 hδβ hQ'2 hδQ hβQ hs'Q hsδ hsβ
  intro q hqQ
  have hqN : q ∈ Subgroup.normalizer (L' : Set G) := hQN hqQ
  have hqQN : (⟨q, hqN⟩ : Subgroup.normalizer (L' : Set G)) ∈ Q.subgroupOf
      (Subgroup.normalizer (L' : Set G)) := Subgroup.mem_subgroupOf.mpr hqQ
  have hq' : ψ ⟨q, hqN⟩ ∈ Q' := Subgroup.mem_map_of_mem ψ hqQN
  have hc : δ * ψ ⟨q, hqN⟩ = ψ ⟨q, hqN⟩ * δ := hcomm _ hq'
  have hcQ : d * q * d⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hdQ q hqQ) (Q.inv_mem hqQ)
  have hψc := hcomm_ker ⟨d, hdN⟩ ⟨q, hqN⟩ hc
  have hc1 : d * q * d⁻¹ * q⁻¹ = 1 := hker _ hcQ hψc
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)

end CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4dProof

end
