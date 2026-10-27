module

public import CFSG.Quasithin.Background.InternalSecB5
public import CFSG.Quasithin.Background.C1PackC127Act
public import CFSG.Quasithin.Vol2.Ch10SecC9S49a
public import CFSG.Quasithin.Vol2.Ch10SecC9S4b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem autI_le_normalizer_autI {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    autI hV X ≤ Subgroup.normalizer (autI hV Y : Set (MulAut (IntMod V hV))) := by
  have key : ∀ φ ∈ autI hV X, ∀ ψ ∈ autI hV Y, φ * ψ * φ⁻¹ ∈ autI hV Y := by
    intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hψ
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (mem_autI hV).2 ⟨_, (Subgroup.mem_normalizer_iff.mp (hXY hg) h).mp hh, rfl⟩
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  refine ⟨key φ hφ ψ, fun h => ?_⟩
  have := key φ⁻¹ (Subgroup.inv_mem _ hφ) _ h
  rwa [inv_inv, show φ⁻¹ * (φ * ψ * φ⁻¹) * φ = ψ by group] at this

theorem autI_thompsonJ_le_ffJ {X S : Subgroup G} (hred : IsTwoReducedIn X V)
    (hS : IsSylowTwoOf S X) : autI hV (thompsonJ S) ≤ ffJ (autI hV X) := by
  refine (autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hS)).trans ?_
  rw [autI_thompsonJ hV hred.2.1]
  exact iSup₂_le fun B hB => iSup_le fun _ =>
    B6.le_ffJ (offenderImages_isFFStarOffender hV hred.1 hred.2.1 hB)

theorem autI_le_centralizer_of_three {X R K : Subgroup G} (hred : IsTwoReducedIn X V)
    (hRX : R ≤ X) (hRn : X ≤ Subgroup.normalizer (R : Set G)) (hRs : Group.IsSolvable ↥R)
    (h3 : ¬ 3 ∣ Nat.card ↥(autI hV R)) (hK : autI hV K ≤ ffJ (autI hV X))
    (hK2 : IsPGroup 2 ↥(autI hV K)) :
    autI hV R ≤ Subgroup.centralizer (autI hV K : Set (MulAut (IntMod V hV))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hs := autI hV X
  set G₁ := ffJ Hs
  set Rs := autI hV R
  have hO2 : pCoreOf 2 Hs = ⊥ := C1Pack.pCoreOf_autI_eq_bot hV hred
  have hG₁ : G₁ = ffJ G₁ := (InternalSec.ffJ_ffJ Hs).symm
  have hG₁N : Hs ≤ Subgroup.normalizer (G₁ : Set (MulAut (IntMod V hV))) :=
    B6.le_normalizer_ffJ Hs
  have hG₁Hs : G₁ ≤ Hs := B6.ffJ_le Hs
  have hcore : ∀ Q : Subgroup (MulAut (IntMod V hV)), Q ≤ Hs →
      Hs ≤ Subgroup.normalizer (Q : Set (MulAut (IntMod V hV))) → pCoreOf 2 Q = ⊥ := by
    intro Q hQ hQn
    rw [eq_bot_iff, ← hO2]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Q).trans hQ)
      (hQn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Q))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Q)
  have hO2G₁ : pCoreOf 2 G₁ = ⊥ := hcore G₁ hG₁Hs hG₁N
  have hRsN : Hs ≤ Subgroup.normalizer (Rs : Set (MulAut (IntMod V hV))) :=
    autI_le_normalizer_autI hV hRn
  have hRsHs : Rs ≤ Hs := autI_mono hV hRX
  have hRss : Group.IsSolvable ↥Rs := by
    rw [show Rs = (convHom hV R (hRX.trans hred.2.1)).range from
      (range_convHom hV R (hRX.trans hred.2.1)).symm]
    exact Group.isSolvable_of_surjective
      (convHom hV R (hRX.trans hred.2.1)).rangeRestrict_surjective
  set N₀ := Rs ⊓ G₁
  have hN₀N : Hs ≤ Subgroup.normalizer (N₀ : Set (MulAut (IntMod V hV))) :=
    fun x hx => mem_normalizer_inf' (hRsN hx) (hG₁N hx)
  have hN₀s : Group.IsSolvable ↥N₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
  have h3N₀ : ¬ 3 ∣ Nat.card ↥N₀ := fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hN₀C : N₀ ≤ Subgroup.centralizer (G₁ : Set (MulAut (IntMod V hV))) :=
    le_centralizer_of_ffJ (fun v => IntMod.sq_eq_one v) hG₁ hO2G₁ inf_le_right hN₀s h3N₀ N₀
      le_rfl (hG₁Hs.trans hN₀N)
  have hN₀odd : Odd (Nat.card ↥N₀) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hzQ : (z : MulAut (IntMod V hV)) ∈ pCoreOf 2 N₀ := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (N := Subgroup.zpowers (z : MulAut (IntMod V hV)))
        ((Subgroup.zpowers_le).mpr z.2) (fun n hn => ?_) ?_ (Subgroup.mem_zpowers _)
      · rw [Subgroup.mem_normalizer_iff]
        intro y
        have hcomm : n * (z : MulAut (IntMod V hV)) = z * n :=
          Subgroup.mem_centralizer_iff.mp (hN₀C z.2) n hn.2
        constructor
        · intro hy
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
          rw [(Commute.zpow_right hcomm m).eq, mul_inv_cancel_right]
        · intro hy
          obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
          refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
          have hc' := (Commute.zpow_right hcomm m).eq
          calc (z : MulAut (IntMod V hV)) ^ m = n⁻¹ * (n * (z : MulAut (IntMod V hV)) ^ m) := by
                group
            _ = n⁻¹ * ((z : MulAut (IntMod V hV)) ^ m * n) := by rw [hc']
            _ = n⁻¹ * (n * y * n⁻¹) * n := by rw [hm]; group
            _ = y := by group
      · exact IsPGroup.of_card (n := 1)
          (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    rw [hcore N₀ (inf_le_left.trans hRsHs) hN₀N, Subgroup.mem_bot] at hzQ
    have := orderOf_one (G := MulAut (IntMod V hV))
    rw [← hzQ, Subgroup.orderOf_coe, hz] at this
    exact absurd this (by norm_num)
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkG₁ : k ∈ G₁ := hK hk
  have hx : ∀ k ∈ autI hV K, r * k * r⁻¹ * k⁻¹ ∈ N₀ := by
    intro k hk
    have hkHs : k ∈ Hs := hG₁Hs (hK hk)
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hRsN hkHs) r⁻¹).mp (Subgroup.inv_mem _ hr)
      rw [show r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) by group]
      exact Subgroup.mul_mem _ hr this
    · have := (Subgroup.mem_normalizer_iff.mp (hG₁N (hRsHs hr)) k).mp (hK hk)
      exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ (hK hk))
  have h1 := commutator_eq_one_of_odd hK2 hN₀odd
    (hN₀C.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hK))) hx k hk
  have : r * k * r⁻¹ = k := by rw [← mul_inv_eq_one]; exact h1
  calc k * r = (r * k * r⁻¹) * r := by rw [this]
    _ = r * k := by group

end CFSG.Quasithin.Vol2.Ch10.SecC
