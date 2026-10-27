module

public import CFSG.Quasithin.Recognition.M12AscModel
public import CFSG.GH74.M12.HypAsc

public section

namespace CFSG.Quasithin

open Subgroup CFSG.GH74.M12.Hyp

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

theorem mem_ascH_conj (z c q : G) : q ∈ ascH (c * z * c⁻¹) ↔ c⁻¹ * q * c ∈ ascH z := by
  rw [ascH, ascH, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * q * c * z = c⁻¹ * (q * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * q) * c := by rw [h]
      _ = z * (c⁻¹ * q * c) := by group
  · intro h
    calc q * (c * z * c⁻¹) = c * ((c⁻¹ * q * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * q * c)) * c⁻¹ := by rw [h]
      _ = (c * z * c⁻¹) * q := by group

theorem mem_ascQ_conj (z c q : G) : q ∈ ascQ (c * z * c⁻¹) ↔ c⁻¹ * q * c ∈ ascQ z := by
  have hmap := CFSG.pCore_map_iso 2 (conjCentralizerEquiv c z)
  rw [mem_ascQ_iff, mem_ascQ_iff]
  constructor
  · rintro ⟨h, hq⟩
    have hh : c⁻¹ * q * c ∈ ascH z := (mem_ascH_conj z c q).1 h
    refine ⟨hh, ?_⟩
    have he : conjCentralizerEquiv c z ⟨c⁻¹ * q * c, hh⟩ = ⟨q, h⟩ :=
      Subtype.ext (by simp only [conjCentralizerEquiv_apply]; group)
    have hq' : (⟨q, h⟩ : ↥(ascH (c * z * c⁻¹))) ∈
        (CFSG.pCore 2 ↥(ascH z)).map (conjCentralizerEquiv c z).toMonoidHom := by
      rw [hmap]; exact hq
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hq'
    have : y = ⟨c⁻¹ * q * c, hh⟩ :=
      (conjCentralizerEquiv c z).injective (by rw [he]; exact hye)
    rw [← this]
    exact hy
  · rintro ⟨hh, hq⟩
    have h : q ∈ ascH (c * z * c⁻¹) := (mem_ascH_conj z c q).2 hh
    refine ⟨h, ?_⟩
    have he : conjCentralizerEquiv c z ⟨c⁻¹ * q * c, hh⟩ = ⟨q, h⟩ :=
      Subtype.ext (by simp only [conjCentralizerEquiv_apply]; group)
    rw [← hmap, ← he]
    exact Subgroup.mem_map_of_mem _ hq

theorem ascQ_conj_eq (z c : G) :
    ascQ (c * z * c⁻¹) = (ascQ z).map (MulAut.conj c).toMonoidHom := by
  ext q
  rw [mem_ascQ_conj, mem_map_conj_iff]

theorem asc03Hyp_conj [Finite G] (hyp : Asc03Hyp G z) (c : G) : Asc03Hyp G (c * z * c⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(ascH z) = 192 := AscModel.card_ascH hyp
  have hloc : LocalHyp ↥(ascH z) (zElt' z) := by
    refine ⟨hcard, hyp.card_core, hyp.extraspecial, hyp.quotient_S3, ?_⟩
    intro x hx q hq hcomm
    have hp3 : IsPGroup 3 ↥(zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
    obtain ⟨P, hP⟩ := hp3.exists_le_sylow
    have hPcard : Nat.card (P : Subgroup ↥(ascH z)) = 3 := by
      have h : Nat.card (P : Subgroup ↥(ascH z)) =
          3 ^ Nat.factorization (Nat.card ↥(ascH z)) 3 := Sylow.card_eq_multiplicity P
      rw [hcard] at h
      have h192 : Nat.factorization 192 3 = 1 := by
        rw [Nat.factorization_def _ Nat.prime_three]
        have h : (192 : ℕ) = 3 * 2 ^ 6 := by norm_num
        rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
          padicValNat.eq_zero_of_not_dvd (by norm_num)]
      rw [h192] at h
      simpa using h
    have hPeq : zpowers x = (P : Subgroup ↥(ascH z)) :=
      Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, Nat.card_zpowers, hx])
    have key := hyp.centralizer_X P q hq (fun y hy => by
      have hy' : y ∈ (P : Subgroup ↥(ascH z)) := hy
      rw [← hPeq] at hy'
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
      exact Commute.zpow_left hcomm n)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 key
    refine Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow]
    exact hn
  have hloc' : LocalHyp ↥(ascH (c * z * c⁻¹)) (zElt' (c * z * c⁻¹)) :=
    LocalHyp.of_mulEquiv (conjCentralizerEquiv c z) (conjCentralizerEquiv_zElt c z) hloc
  have hz2 : orderOf (c * z * c⁻¹) = 2 := by
    have := (MulAut.conj c).orderOf_eq z
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hyp.orderTwo
  have hmap := CFSG.pCore_map_iso 2 (conjCentralizerEquiv c z)
  obtain ⟨g₀, hg₀, q, hq, hqe⟩ := hyp.not_weakly_closed
  refine asc03Hyp_of_local (c * z * c⁻¹) hz2 hloc' ⟨c * g₀ * c⁻¹, ?_, conjCentralizerEquiv c z q, ?_, ?_⟩
  · intro h
    apply hg₀
    calc g₀ * z * g₀⁻¹ = c⁻¹ * ((c * g₀ * c⁻¹) * (c * z * c⁻¹) * (c * g₀ * c⁻¹)⁻¹) * c := by group
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [h]
      _ = z := by group
  · rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hq
  · rw [conjCentralizerEquiv_apply, hqe]
    group

@[expose] def AscModel.conj (m : AscModel z) (c : G) : AscModel (c * z * c⁻¹) where
  φ := (conjCentralizerEquiv c z).symm.trans m.φ
  hz := by
    have h : (conjCentralizerEquiv c z).symm (zElt' (c * z * c⁻¹)) = zElt' z := by
      rw [MulEquiv.symm_apply_eq]; rfl
    show (m.φ ((conjCentralizerEquiv c z).symm (zElt' (c * z * c⁻¹))) :
      Equiv.Perm (Fin 12)) = _
    rw [h]
    exact m.hz

end CFSG.Quasithin
