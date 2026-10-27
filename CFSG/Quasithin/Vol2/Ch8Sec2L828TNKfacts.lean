module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNCover
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNAct
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section NKfacts

variable {G : Type} [Group G] [Finite G]

theorem s828N_Kfacts {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k)
    (hX6 : AlternatingNatural
      (autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
        (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) ⊤ ⊥ 6)
    (hU16 : Nat.card ↥(ch82U (fsuV T I) h) = 16)
    {K : Subgroup G} (hLUK : ch82LU L (ch82U (fsuV T I) h) ≤ K)
    (hKN : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcc : ⁅K, Subgroup.centralizer (ch82U (fsuV T I) h : Set G)⁆ ≤ pCoreOf 2 K) :
    ¬ 5 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) ∧
      ¬ 9 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) ∧
      (∃ f ∈ K, f ^ 5 = 1 ∧ f ∉ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) ∧
      (∀ S : Sylow 3 ↥K, ¬ IsCyclic (S : Subgroup ↥K)) := by
  classical
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hcomm : ∀ a b : ↥(ch82U (fsuV T I) h), a * b = b * a := by
    intro a b
    apply Subtype.ext
    have := mul_comm (⟨(a : G), hUV a.2⟩ : ↥(fsuV T I)) ⟨(b : G), hUV b.2⟩
    exact congrArg (fun z : ↥(fsuV T I) => (z : G)) this
  have hsq : ∀ a : ↥(ch82U (fsuV T I) h), a ^ 2 = 1 := fun a => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hV.2 _ (hUV a.2))
  have hMA : Nat.card (MulAut ↥(ch82U (fsuV T I) h)) = 20160 :=
    s828N_card_mulAut_sixteen hU16 hcomm hsq
  set ψ0 := s828NAct (ch82U (fsuV T I) h) K hKN with hψ0
  have hR : Nat.card ↥ψ0.range ∣ 20160 := hMA ▸ Subgroup.card_subgroup_dvd_card _
  have h360 : 360 ∣ Nat.card ↥ψ0.range := s828N_dvd_range c hX6 hLUK hKN
  have h5 : 5 ∣ Nat.card ↥ψ0.range := (by norm_num : 5 ∣ 360).trans h360
  have h9 : 9 ∣ Nat.card ↥ψ0.range := (by norm_num : 9 ∣ 360).trans h360
  have hno9 : ∀ r : ↥ψ0.range, r ^ 9 = 1 → r ^ 3 = 1 := by
    intro r hr
    apply Subtype.ext
    have h1 : ((r : MulAut ↥(ch82U (fsuV T I) h))) ^ 9 = 1 := by
      have := congrArg Subtype.val hr
      simpa using this
    have h2 := pow_three_eq_one_of_card_828 hU16 h1
    simpa using h2
  have hcent : ∀ x ∈ ψ0.rangeRestrict.ker, ∀ y : ↥K, ⁅y, x⁆ ∈ CFSG.pCore 2 ↥K := by
    intro x hx y
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hψ0, s828NAct_eq_one_iff] at hx
    have h1 : ⁅(y : G), (x : G)⁆ ∈ ⁅K, Subgroup.centralizer (ch82U (fsuV T I) h : Set G)⁆ :=
      Subgroup.commutator_mem_commutator y.2 hx
    exact (CFSG.mem_openPCoreOf_iff (⁅y, x⁆ : ↥K)).mp (hcc h1)
  obtain ⟨h5k, h9k, ⟨f, hf5, hfψ⟩, hnc⟩ := L828N.s828N_cover ψ0.rangeRestrict
    ψ0.rangeRestrict_surjective hq hcent hR h5 h9 hno9
  have hker : Nat.card ψ0.rangeRestrict.ker =
      Nat.card ↥(K ⊓ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact s828N_card_ker hKN
  refine ⟨hker ▸ h5k, hker ▸ h9k, ⟨(f : G), f.2, ?_, ?_⟩, hnc⟩
  · have := congrArg (fun z : ↥K => (z : G)) hf5
    simpa using this
  · intro hfc
    apply hfψ
    have : ψ0 f = 1 := (s828NAct_eq_one_iff hKN f).mpr hfc
    exact Subtype.ext this

end NKfacts

end CFSG.Quasithin.H13
