module

public import CFSG.Quasithin.EmptyFaithful.S143IF
public import CFSG.Quasithin.EmptyFaithful.S143Fuse
public import CFSG.Quasithin.EmptyFaithful.S143IE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Lin2

namespace S143

section CaseB

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.conj_mem_qOf_of_not_commute (c18a : Concl18a T M g) {t₀ s y z : G}
    (htT : t₀ ∈ T) (htRQ : t₀ ∉ rOf T M ⊔ qOf T) (hsT : s ∈ T) (hsRQ : s ∉ rOf T M ⊔ qOf T)
    (hs2 : s * s = 1) (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hys : y * z * y⁻¹ = s) (hB : ¬ ∀ v ∈ VZ T M, s * v = v * s) : y⁻¹ * z * y ∈ qOf T := by
  have h := c.h1281
  have hs := c.swapData_of_involution hrW hrV hr2 htT htRQ hsT hsRQ hs2 c18a.rq_index
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hzV : z ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hz
  have hzs : z * s = s * z := Subgroup.mem_centralizer_iff.mp (hTH hsT) z hz
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (fun w hw => c.VZ_sq hw) ha hb
  have hzC : z ∈ VZ T M ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨hzV, Subgroup.mem_centralizer_singleton_iff.mpr hzs⟩
  have hCcard : Nat.card ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)) = 2 := by
    have hdvd : Nat.card ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)) ∣ Nat.card (VZ T M) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [h.rank_two] at hdvd
    have hne4 : Nat.card ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)) ≠ 4 := by
      intro h4
      apply hB
      have hall : VZ T M ⊓ Subgroup.centralizer ({s} : Set G) = VZ T M :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, h.rank_two])
      intro v hv
      have hv' : v ∈ VZ T M ⊓ Subgroup.centralizer ({s} : Set G) := by rw [hall]; exact hv
      exact (Subgroup.mem_centralizer_singleton_iff.mp hv'.2).symm
    have hne1 : Nat.card ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)) ≠ 1 := by
      intro h1
      have hbot : VZ T M ⊓ Subgroup.centralizer ({s} : Set G) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _ h1
      have : z ∈ (⊥ : Subgroup G) := hbot ▸ hzC
      exact hz1 (Subgroup.mem_bot.mp this)
    have hpos : 0 < Nat.card ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)) := Nat.card_pos
    have hle : Nat.card ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)) = n at hdvd hne4 hne1 hpos hle
    interval_cases n
    · exact absurd rfl hne1
    · rfl
    · exact absurd hdvd (by norm_num)
    · exact absurd rfl hne4
  obtain ⟨w₀, -, hw₀⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(VZ T M ⊓ Subgroup.centralizer ({s} : Set G)))).mp hCcard
  have hz_eq : ∀ x ∈ VZ T M ⊓ Subgroup.centralizer ({s} : Set G), x ≠ 1 → x = z := by
    intro x hx hx1
    have h1 := hw₀ ⟨x, hx⟩ (fun he => hx1 (congrArg Subtype.val he))
    have h2 := hw₀ ⟨z, hzC⟩ (fun he => hz1 (congrArg Subtype.val he))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hτN : ∀ n ∈ VZ T M, s * n * s⁻¹ ∈ VZ T M := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp (c.T_mem_normalizer_VZ hsT) n).mp hn
  have H3 := H3_of_card hs.tt hτN hVab (fun w hw => c.VZ_sq hw) (by rw [hCcard, h.rank_two])
  have hP := hs.card_C H3
  rw [h.rank_two, c.card_Ac hrW hrV hr2, hCcard] at hP
  have hP8 : Nat.card ↥(rOf T M ⊓ Subgroup.centralizer ({s} : Set G)) = 8 := by omega
  have hPmem : ∀ w, w ∈ conjSubgroup (rOf T M ⊓ Subgroup.centralizer ({s} : Set G)) y ↔
      y * w * y⁻¹ ∈ rOf T M ⊓ Subgroup.centralizer ({s} : Set G) := fun w => mem_conjSubgroup_iff
  have hP'H : conjSubgroup (rOf T M ⊓ Subgroup.centralizer ({s} : Set G)) y ≤ mcOf T := by
    intro w hw
    have hwP := (hPmem w).mp hw
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hwP.2
    apply c.mem_mcOf_of_comm hz hz1
    have h1 : y * (w * z) * y⁻¹ = y * (z * w) * y⁻¹ := by
      calc y * (w * z) * y⁻¹ = (y * w * y⁻¹) * (y * z * y⁻¹) := by group
        _ = (y * w * y⁻¹) * s := by rw [hys]
        _ = s * (y * w * y⁻¹) := hc
        _ = (y * z * y⁻¹) * (y * w * y⁻¹) := by rw [hys]
        _ = y * (z * w) * y⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hP'8 : Nat.card ↥(conjSubgroup (rOf T M ⊓ Subgroup.centralizer ({s} : Set G)) y) = 8 := by
    rw [S143.card_conjSubgroup, hP8]
  have huniq : ∀ w ∈ conjSubgroup (rOf T M ⊓ Subgroup.centralizer ({s} : Set G)) y,
      w * w = 1 → w ≠ 1 → w = y⁻¹ * z * y := by
    intro w hw hw2 hw1
    have hwP := (hPmem w).mp hw
    have hwx : w = y⁻¹ * (y * w * y⁻¹) * y := by group
    have hx2 : (y * w * y⁻¹) * (y * w * y⁻¹) = 1 := by
      calc (y * w * y⁻¹) * (y * w * y⁻¹) = y * (w * w) * y⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    have hxs : s * (y * w * y⁻¹) = (y * w * y⁻¹) * s :=
      (Subgroup.mem_centralizer_singleton_iff.mp hwP.2).symm
    have hxV : y * w * y⁻¹ ∈ VZ T M := by
      rcases hs.inv_mem_UV _ hwP.1 hx2 with hxU | hxU
      · exact hs.fixed_U hxU hxs
      · exact hs.fixed_V hxU hxs
    have hxC : y * w * y⁻¹ ∈ VZ T M ⊓ Subgroup.centralizer ({s} : Set G) := ⟨hxV, hwP.2⟩
    have hx1 : y * w * y⁻¹ ≠ 1 := by
      intro h1
      apply hw1
      rw [hwx, h1]
      group
    rw [hwx, hz_eq _ hxC hx1]
  exact c.mem_qOf_of_card_eight hP'H hP'8 huniq

end CaseB

theorem lemma_14_3_21_two : Lemma14321Two := by
  intro G _ _ T M g A t c c18 c19 _ s hsT hsRQ hs2 y z hz hz1 hys
  have hs2' : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs2, sq] at this
  obtain ⟨r, hrW, hrV, hr2, rfl⟩ := c.exists_Ac_eq c18.b
  have hζ : y⁻¹ * z * y ∈ qOf T := by
    by_cases hA : ∀ v ∈ VZ T M, s * v = v * s
    · exact c.conj_mem_qOf_of_commute hrW hrV hr2 c18.a c18.b.t_mem c18.b.t_nmem hsT hsRQ hs2' hz
        hz1 hys hA
    · exact c.conj_mem_qOf_of_not_commute hrW hrV hr2 c18.a c18.b.t_mem c18.b.t_nmem hsT hsRQ
        hs2' hz hz1 hys hA
  obtain ⟨a, ha, b, hb, hab⟩ := c.exists_commutator_of_conj_mem_qOf c19.a.q_eq hz hz1 hys hζ
  exact c.not_commutator_of_not_mem_rq c18.a.rq_index hsT hsRQ a ha b hb hab

end S143

end CFSG.Quasithin
