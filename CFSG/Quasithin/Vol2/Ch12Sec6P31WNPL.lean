module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WInp
public import CFSG.Quasithin.Vol2.Ch12Sec6L19a
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WNPLCLV
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WNPLSyl
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WNPLSound
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WNPLConj

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126L19a

theorem noPermL_w31_holds : NoPermL_w31 := by
  unfold NoPermL_w31
  intro G _ _ T L V _ F hH hVC P hPL p hp hp3 hPp hPT
  by_contra hPne
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    subst h4
    norm_num at hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let ψ := psi F hH
  have hψ : Function.Surjective ψ := psi_surjective F hH
  have hA : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := S126L1a.card_A8
  have hK : ¬ p ∣ Nat.card ψ.ker :=
    CFSG.Quasithin.H13.NPLCLV.not_dvd_card_ker (CFSG.pCore 2 ↥L) CFSG.pCore_isPGroup
      hH.hyp.quasisimple ψ hψ hA p hp5
  have hPnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hPp).1 hPnt
  have hdvd : p ∣ Nat.card ↥P := by
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let xL : ↥L := ⟨(x0 : G), hPL x0.2⟩
  have hxp : xL ^ p = 1 := by
    apply Subtype.ext
    have h := congrArg Subtype.val (pow_orderOf_eq_one x0)
    rw [hx0] at h
    simpa [xL] using h
  have hxne : xL ≠ 1 := by
    intro h
    have h' : (x0 : G) = 1 := congrArg Subtype.val h
    have h'' : x0 = 1 := Subtype.ext h'
    rw [h'', orderOf_one] at hx0
    exact hp.one_lt.ne' hx0.symm
  have hσp : ψ xL ^ p = 1 := by
    rw [← map_pow, hxp, map_one]
  have hσne : ψ xL ≠ 1 := by
    intro h
    have hk : xL ∈ ψ.ker := (MonoidHom.mem_ker).2 h
    have hkp : (⟨xL, hk⟩ : ψ.ker) ^ p = 1 := by
      apply Subtype.ext
      simpa using hxp
    have hkne : (⟨xL, hk⟩ : ψ.ker) ≠ 1 := by
      intro h1
      apply hxne
      exact congrArg Subtype.val h1
    have hord : orderOf (⟨xL, hk⟩ : ψ.ker) = p := orderOf_eq_prime hkp hkne
    apply hK
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hσord : orderOf (ψ xL) = p := orderOf_eq_prime hσp hσne
  have hpA : p ∣ 20160 := by
    rw [← hA, ← hσord]
    exact orderOf_dvd_natCard _
  have hp57 : p = 5 ∨ p = 7 := CFSG.Quasithin.H13.NPLSyl.prime_dvd_20160 hp hp5 hpA
  have hσ57 : ψ xL ^ 5 = 1 ∨ ψ xL ^ 7 = 1 := by
    rcases hp57 with h | h
    · left
      rw [← h]
      exact hσp
    · right
      rw [← h]
      exact hσp
  let SA : Subgroup ↥(alternatingGroup (Fin 8)) := ((T ⊓ L).subgroupOf L).map ψ
  have hSA : Nat.card SA = 64 :=
    CFSG.Quasithin.H13.NPLSyl.card_map_sylow hH.hyp.normalizes hH.hyp.sylow ψ hψ hA
  have hPp' : IsPGroup p ↥(P.subgroupOf L) := IsPGroup.comap_subtype hPp
  have hxmem : xL ∈ P.subgroupOf L := Subgroup.mem_subgroupOf.2 x0.2
  have hZ : Nat.card ↥(Subgroup.closure (insert (ψ xL) ((SA : Subgroup _) : Set ↥(alternatingGroup (Fin 8))))) ≤ p * 64 :=
    CFSG.Quasithin.H13.NPLSyl.closure_card_le hPL hPT hH.hyp.sylow hH.hyp.normalizes ψ hψ hA
      hp hp5 hPp' xL hxmem
  let e : ↥(alternatingGroup (Fin 8)) →* Equiv.Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype
  have he : Function.Injective e := Subtype.val_injective
  let SP : Subgroup (Equiv.Perm (Fin 8)) := SA.map e
  have hSP : Nat.card SP = 64 := by
    rw [← hSA]
    exact Subgroup.card_map_of_injective he
  have hSP_le : SP ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨a, _, rfl⟩
    exact a.2
  have hZP : Nat.card ↥(Subgroup.closure (insert (e (ψ xL))
      ((SP : Subgroup _) : Set (Equiv.Perm (Fin 8))))) ≤ p * 64 := by
    have himg : ((SP : Subgroup _) : Set (Equiv.Perm (Fin 8))) =
        e '' ((SA : Subgroup _) : Set ↥(alternatingGroup (Fin 8))) := Subgroup.coe_map e SA
    have hmap : (Subgroup.closure (insert (ψ xL)
        ((SA : Subgroup _) : Set ↥(alternatingGroup (Fin 8))))).map e =
        Subgroup.closure (insert (e (ψ xL)) (e '' ((SA : Subgroup _) : Set ↥(alternatingGroup (Fin 8))))) := by
      rw [MonoidHom.map_closure, Set.image_insert_eq]
    rw [himg, ← hmap, Subgroup.card_map_of_injective he]
    exact hZ
  obtain ⟨g, hg⟩ := NPLConj.exists_conj_perm NPLSound.S0 SP NPLSound.S0_le_alt hSP_le
    NPLSound.S0_card hSP
  have himg2 : (fun x => g * x * g⁻¹) '' ((SP : Subgroup _) : Set (Equiv.Perm (Fin 8))) =
      ((NPLSound.S0 : Subgroup _) : Set (Equiv.Perm (Fin 8))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hg x).1 hx
    · intro hy
      refine ⟨g⁻¹ * y * g, (hg (g⁻¹ * y * g)).2 ?_, ?_⟩
      · have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [h1]
        exact hy
      · show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hcc := NPLConj.card_closure_conj g (e (ψ xL)) ((SP : Subgroup _) : Set (Equiv.Perm (Fin 8)))
  rw [himg2] at hcc
  have hσ'ne : g * e (ψ xL) * g⁻¹ ≠ 1 := by
    intro h
    have h1 : e (ψ xL) = 1 := by
      have h2 : e (ψ xL) = g⁻¹ * (g * e (ψ xL) * g⁻¹) * g := by group
      rw [h2, h]
      group
    apply hσne
    apply he
    rw [map_one]
    exact h1
  have hσ'pow : (g * e (ψ xL) * g⁻¹) ^ 5 = 1 ∨ (g * e (ψ xL) * g⁻¹) ^ 7 = 1 := by
    rcases hσ57 with h | h
    · left
      rw [conj_pow, ← map_pow, h, map_one]
      group
    · right
      rw [conj_pow, ← map_pow, h, map_one]
      group
  have big := NPLSound.big_of_ne_one (g * e (ψ xL) * g⁻¹) hσ'ne hσ'pow
  have hp448 : p * 64 ≤ 448 := by
    rcases hp57 with h | h <;> omega
  omega

end CFSG.Quasithin.H13

end
